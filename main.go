package main

import (
	"context"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"math"
	"math/rand"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
	"time"
)

// ==========================================
// 全局状态与结构定义
// ==========================================

// TaskStatus 包含了录制文件大小和此时长的字段
type TaskStatus struct {
	Platform   string `json:"platform"`
	RoomID     string `json:"room_id"`
	AnchorName string `json:"anchor_name"`
	Quality    string `json:"quality"`
	Status     string `json:"status"`
	UpdateTime string `json:"update_time"`
	IsPaused   bool   `json:"is_paused"`
	FileSize   string `json:"file_size"`
	Duration   string `json:"duration"`

	startTime time.Time `json:"-"` // 内部私有字段：用于记录本次录制开始的绝对时间戳
}

var (
	globalConfig  *Config
	activeTasks   sync.Map
	globalStatus  sync.Map
	globalCookies *CookieConfig
	cookieMutex   sync.RWMutex

	taskStates    sync.Map // key: platform_roomID, value: "running", "paused", "deleted"
	activeCancels sync.Map // key: platform_roomID, value: context.CancelFunc
)

func updateStatus(platform, roomID, anchorName, quality, statusMsg string) {
	key := platform + "_" + roomID
	now := time.Now()
	var sTime time.Time

	// 尝试继承并处理现有的名称和 startTime
	if existing, ok := globalStatus.Load(key); ok {
		oldTask := existing.(*TaskStatus)
		if anchorName == "" {
			anchorName = oldTask.AnchorName
		}
		// 管理录制开始时间
		if statusMsg == "录制中" {
			if oldTask.Status != "录制中" {
				sTime = now // 刚刚由其他状态切入录制，记录此刻为起始时间
			} else {
				sTime = oldTask.startTime // 继续保持原有的起始时间
			}
		}
	} else {
		// 第一次记录
		if statusMsg == "录制中" {
			sTime = now
		}
	}

	if anchorName == "" {
		anchorName = roomID
	}

	state, _ := taskStates.Load(key)
	isPaused := state == "paused"
	if isPaused {
		statusMsg = "已暂停"
	}

	globalStatus.Store(key, &TaskStatus{
		Platform:   platform,
		RoomID:     roomID,
		AnchorName: anchorName,
		Quality:    quality,
		Status:     statusMsg,
		UpdateTime: time.Now().Format("2006-01-02 15:04:05"),
		IsPaused:   isPaused,
		startTime:  sTime, // 将时间存于内存
	})
}

type Config struct {
	Douyin        []string `json:"douyin"`
	Kuaishou      []string `json:"kuaishou"`
	Soop          []string `json:"soop"`
	Quality       string   `json:"quality"`
	SegmentTime   int      `json:"segment_time"`
	CheckInterval int      `json:"check_interval"`
	SavePath      string   `json:"save_path"` // 新增：自定义录制文件保存路径
}

type CookieConfig struct {
	Douyin   string `json:"douyin"`
	Kuaishou string `json:"kuaishou"`
	Soop     string `json:"soop"`
}

type Platform interface {
	GetPlatformName() string
	GetStreamURL(roomID string, quality string) (streamURL string, anchorName string, err error)
}

// ==========================================
// 核心加密算法复刻 (SM3, RC4, a_bogus)
// ==========================================

func rc4Encrypt(plaintext, key string) string {
	s := make([]int, 256)
	for i := 0; i < 256; i++ {
		s[i] = i
	}
	j := 0
	for i := 0; i < 256; i++ {
		j = (j + s[i] + int(key[i%len(key)])) % 256
		s[i], s[j] = s[j], s[i]
	}
	i := 0
	j = 0
	res := make([]byte, len(plaintext))
	for k := 0; k < len(plaintext); k++ {
		i = (i + 1) % 256
		j = (j + s[i]) % 256
		s[i], s[j] = s[j], s[i]
		t := (s[i] + s[j]) % 256
		res[k] = byte(int(plaintext[k]) ^ s[t])
	}
	return string(res)
}

type SM3 struct {
	reg   []uint32
	chunk []byte
	size  uint64
}

func NewSM3() *SM3 {
	sm3 := &SM3{}
	sm3.Reset()
	return sm3
}

func (s *SM3) Reset() {
	s.reg = []uint32{
		1937774191, 1226093241, 388252375, 3666478592,
		2842636476, 372324522, 3817729613, 2969243214,
	}
	s.chunk = []byte{}
	s.size = 0
}

func (s *SM3) leftRotate(x uint32, n int) uint32 {
	n &= 0x1f
	if n == 0 {
		return x
	}
	return (x << n) | (x >> (32 - n))
}

func (s *SM3) getT(j int) uint32 {
	if j < 16 {
		return 2043430169
	}
	return 2055708042
}

func (s *SM3) ff(j int, x, y, z uint32) uint32 {
	if j < 16 {
		return x ^ y ^ z
	}
	return (x & y) | (x & z) | (y & z)
}

func (s *SM3) gg(j int, x, y, z uint32) uint32 {
	if j < 16 {
		return x ^ y ^ z
	}
	return (x & y) | (^x & z)
}

func (s *SM3) compress(data []byte) {
	w := make([]uint32, 132)
	for t := 0; t < 16; t++ {
		w[t] = binary.BigEndian.Uint32(data[4*t : 4*t+4])
	}
	for j := 16; j < 68; j++ {
		a := w[j-16] ^ w[j-9] ^ s.leftRotate(w[j-3], 15)
		w[j] = a ^ s.leftRotate(a, 15) ^ s.leftRotate(a, 23) ^ s.leftRotate(w[j-13], 7) ^ w[j-6]
	}
	for j := 0; j < 64; j++ {
		w[j+68] = w[j] ^ w[j+4]
	}
	a, b, c, d, e, f, g, h := s.reg[0], s.reg[1], s.reg[2], s.reg[3], s.reg[4], s.reg[5], s.reg[6], s.reg[7]
	for j := 0; j < 64; j++ {
		ss1 := s.leftRotate((s.leftRotate(a, 12) + e + s.leftRotate(s.getT(j), j)), 7)
		ss2 := ss1 ^ s.leftRotate(a, 12)
		tt1 := s.ff(j, a, b, c) + d + ss2 + w[j+68]
		tt2 := s.gg(j, e, f, g) + h + ss1 + w[j]
		d = c
		c = s.leftRotate(b, 9)
		b = a
		a = tt1
		h = g
		g = s.leftRotate(f, 19)
		f = e
		e = tt2 ^ s.leftRotate(tt2, 9) ^ s.leftRotate(tt2, 17)
	}
	s.reg[0] ^= a
	s.reg[1] ^= b
	s.reg[2] ^= c
	s.reg[3] ^= d
	s.reg[4] ^= e
	s.reg[5] ^= f
	s.reg[6] ^= g
	s.reg[7] ^= h
}

func (s *SM3) Write(data string) {
	b := []byte(data)
	s.size += uint64(len(b))
	f := 64 - len(s.chunk)
	if len(b) < f {
		s.chunk = append(s.chunk, b...)
	} else {
		s.chunk = append(s.chunk, b[:f]...)
		for len(s.chunk) >= 64 {
			s.compress(s.chunk)
			b = b[f:]
			if len(b) < 64 {
				s.chunk = b
				break
			}
			s.chunk = b[:64]
			f = 64
		}
	}
}

func (s *SM3) Sum() []byte {
	bitLength := s.size * 8
	s.chunk = append(s.chunk, 0x80)
	for (len(s.chunk)+8)%64 != 0 {
		s.chunk = append(s.chunk, 0)
	}
	lenBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(lenBytes, bitLength)
	s.chunk = append(s.chunk, lenBytes...)
	for i := 0; i < len(s.chunk); i += 64 {
		s.compress(s.chunk[i : i+64])
	}
	res := make([]byte, 32)
	for i := 0; i < 8; i++ {
		binary.BigEndian.PutUint32(res[4*i:], s.reg[i])
	}
	s.Reset()
	return res
}

func resultEncrypt(longStr, num string) string {
	encodingTables := map[string]string{
		"s0": "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=",
		"s1": "Dkdpgh4ZKsQB80/Mfvw36XI1R25+WUAlEi7NLboqYTOPuzmFjJnryx9HVGcaStCe=",
		"s2": "Dkdpgh4ZKsQB80/Mfvw36XI1R25-WUAlEi7NLboqYTOPuzmFjJnryx9HVGcaStCe=",
		"s3": "ckdp1h4ZKsUB80/Mfvw36XIgR25+WQAlEi7NLboqYTOPuzmFjJnryx9HVGDaStCe",
		"s4": "Dkdpgh2ZmsQB80/MfvV36XI1R45-WUAlEixNLwoqYTOPuzKFjJnry79HbGcaStCe",
	}
	table := encodingTables[num]
	masks := []int{16515072, 258048, 4032, 63}
	shifts := []int{18, 12, 6, 0}
	var res strings.Builder
	roundNum := 0
	getLongInt := func(round int, s string) int {
		idx := round * 3
		var ch1, ch2, ch3 int
		if idx < len(s) {
			ch1 = int(s[idx])
		}
		if idx+1 < len(s) {
			ch2 = int(s[idx+1])
		}
		if idx+2 < len(s) {
			ch3 = int(s[idx+2])
		}
		return (ch1 << 16) | (ch2 << 8) | ch3
	}
	longInt := getLongInt(roundNum, longStr)
	totalChars := int(math.Ceil(float64(len(longStr)) / 3.0 * 4.0))
	for i := 0; i < totalChars; i++ {
		if i/4 != roundNum {
			roundNum++
			longInt = getLongInt(roundNum, longStr)
		}
		index := i % 4
		charIndex := (longInt & masks[index]) >> shifts[index]
		res.WriteByte(table[charIndex])
	}
	return res.String()
}

func generRandom(randomNum int, option []int) []int {
	byte1 := randomNum & 255
	byte2 := (randomNum >> 8) & 255
	return []int{
		(byte1 & 170) | (option[0] & 85),
		(byte1 & 85) | (option[0] & 170),
		(byte2 & 170) | (option[1] & 85),
		(byte2 & 85) | (option[1] & 170),
	}
}

func generateRandomStr() string {
	r1 := rand.Float64()
	r2 := rand.Float64()
	r3 := rand.Float64()

	var bytes []int
	bytes = append(bytes, generRandom(int(r1*10000), []int{3, 45})...)
	bytes = append(bytes, generRandom(int(r2*10000), []int{1, 0})...)
	bytes = append(bytes, generRandom(int(r3*10000), []int{1, 5})...)

	var sb strings.Builder
	for _, b := range bytes {
		sb.WriteByte(byte(b))
	}
	return sb.String()
}

func generateABogus(params, userAgent string) string {
	windowEnvStr := "1920|1080|1920|1040|0|30|0|0|1872|92|1920|1040|1857|92|1|24|Win32"
	suffix := "cus"
	arguments := []int{0, 1, 14}

	sm3 := NewSM3()
	startTime := int(time.Now().UnixNano() / 1e6)

	sm3.Write(params + suffix)
	hash1 := string(sm3.Sum())
	sm3.Write(hash1)
	urlSearchParamsList := sm3.Sum()

	sm3.Write(suffix)
	hash2 := string(sm3.Sum())
	sm3.Write(hash2)
	cus := sm3.Sum()

	uaKey := string([]byte{0, 1, 14})
	uaEnc := rc4Encrypt(userAgent, uaKey)
	uaB64 := resultEncrypt(uaEnc, "s3")
	sm3.Write(uaB64)
	uaHash := sm3.Sum()

	b := make(map[int]int)
	b[8] = 3
	b[10] = startTime + 100
	b[16] = startTime
	b[18] = 44

	splitToBytes := func(num int) []int {
		return []int{(num >> 24) & 255, (num >> 16) & 255, (num >> 8) & 255, num & 255}
	}

	stBytes := splitToBytes(b[16])
	b[20], b[21], b[22], b[23] = stBytes[0], stBytes[1], stBytes[2], stBytes[3]
	b[24] = (b[16] >> 32) & 255
	b[25] = (b[16] >> 40) & 255

	arg0 := splitToBytes(arguments[0])
	b[26], b[27], b[28], b[29] = arg0[0], arg0[1], arg0[2], arg0[3]
	b[30] = (arguments[1] >> 8) & 255
	b[31] = arguments[1] & 255
	arg1 := splitToBytes(arguments[1])
	b[32], b[33] = arg1[0], arg1[1]
	arg2 := splitToBytes(arguments[2])
	b[34], b[35], b[36], b[37] = arg2[0], arg2[1], arg2[2], arg2[3]

	b[38] = int(urlSearchParamsList[21])
	b[39] = int(urlSearchParamsList[22])
	b[40] = int(cus[21])
	b[41] = int(cus[22])
	b[42] = int(uaHash[23])
	b[43] = int(uaHash[24])

	etBytes := splitToBytes(b[10])
	b[44], b[45], b[46], b[47] = etBytes[0], etBytes[1], etBytes[2], etBytes[3]
	b[48] = b[8]
	b[49] = (b[10] >> 32) & 255
	b[50] = (b[10] >> 40) & 255

	pageId := 110624
	b[51] = pageId
	pIdBytes := splitToBytes(pageId)
	b[52], b[53], b[54], b[55] = pIdBytes[0], pIdBytes[1], pIdBytes[2], pIdBytes[3]

	aid := 6383
	b[56] = aid
	b[57] = aid & 255
	b[58] = (aid >> 8) & 255
	b[59] = (aid >> 16) & 255
	b[60] = (aid >> 24) & 255

	winEnvList := []byte(windowEnvStr)
	b[64] = len(winEnvList)
	b[65] = b[64] & 255
	b[66] = (b[64] >> 8) & 255
	b[69], b[70], b[71] = 0, 0, 0

	xorSum := b[18] ^ b[20] ^ b[26] ^ b[30] ^ b[38] ^ b[40] ^ b[42] ^ b[21] ^ b[27] ^ b[31] ^
		b[35] ^ b[39] ^ b[41] ^ b[43] ^ b[22] ^ b[28] ^ b[32] ^ b[36] ^ b[23] ^ b[29] ^
		b[33] ^ b[37] ^ b[44] ^ b[45] ^ b[46] ^ b[47] ^ b[48] ^ b[49] ^ b[50] ^ b[24] ^
		b[25] ^ b[52] ^ b[53] ^ b[54] ^ b[55] ^ b[57] ^ b[58] ^ b[59] ^ b[60] ^ b[65] ^
		b[66] ^ b[70] ^ b[71]
	b[72] = xorSum

	var bb []byte
	indices := []int{
		18, 20, 52, 26, 30, 34, 58, 38, 40, 53, 42, 21,
		27, 54, 55, 31, 35, 57, 39, 41, 43, 22, 28, 32,
		60, 36, 23, 29, 33, 37, 44, 45, 59, 46, 47, 48,
		49, 50, 24, 25, 65, 66, 70, 71,
	}
	for _, idx := range indices {
		bb = append(bb, byte(b[idx]))
	}
	bb = append(bb, winEnvList...)
	bb = append(bb, byte(b[72]))

	prefix := generateRandomStr()
	body := rc4Encrypt(string(bb), string([]byte{121}))
	return resultEncrypt(prefix+body, "s4") + "="
}

// ==========================================
// 辅助工具函数
// ==========================================

func checkFFmpeg() {
	_, err := exec.LookPath("ffmpeg")
	if err != nil {
		log.Println("【严重警告】系统中未找到 ffmpeg 工具！程序无法录制。请安装 ffmpeg。")
	}
}

func extractRoomID(input string) string {
	input = strings.TrimSpace(input)
	if strings.HasPrefix(input, "http://") || strings.HasPrefix(input, "https://") {
		u, err := url.Parse(input)
		if err == nil {
			path := strings.Trim(u.Path, "/")
			segments := strings.Split(path, "/")
			if len(segments) > 0 {
				return segments[len(segments)-1]
			}
		}
	}
	return input
}

func sanitizeFileName(name string) string {
	invalidChars := []string{"\\", "/", ":", "*", "?", "\"", "<", ">", "|"}
	for _, char := range invalidChars {
		name = strings.ReplaceAll(name, char, "_")
	}
	return strings.TrimSpace(name)
}

func formatDuration(d time.Duration) string {
	h := int(d.Hours())
	m := int(d.Minutes()) % 60
	s := int(d.Seconds()) % 60
	if h > 0 {
		return fmt.Sprintf("%02d小时%02d分%02d秒", h, m, s)
	}
	return fmt.Sprintf("%02d分%02d秒", m, s)
}

// 计算指定文件夹大小
func getDirSizeStr(path string) string {
	var size int64
	err := filepath.Walk(path, func(_ string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if !info.IsDir() {
			size += info.Size()
		}
		return nil
	})
	if err != nil || size == 0 {
		return "0 B"
	}
	return formatBytes(size)
}

// 格式化字节大小输出 MB/GB
func formatBytes(b int64) string {
	const unit = 1024
	if b < unit {
		return fmt.Sprintf("%d B", b)
	}
	div, exp := int64(unit), 0
	for n := b / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.2f %cB", float64(b)/float64(div), "KMGTPE"[exp])
}

func formatQualityName(quality string) string {
	switch quality {
	case "uhd":
		return "蓝光/超清"
	case "hd":
		return "高清"
	case "sd":
		return "标清"
	default:
		return "未知画质"
	}
}

// ==========================================
// 抖音平台实现部分 (集成 a_bogus 签名)
// ==========================================

type DouyinPlatform struct{}

func (d *DouyinPlatform) GetPlatformName() string { return "Douyin" }

func (d *DouyinPlatform) GetStreamURL(roomID string, quality string) (string, string, error) {
	params := url.Values{}
	params.Set("aid", "6383")
	params.Set("app_name", "douyin_web")
	params.Set("live_id", "1")
	params.Set("device_platform", "web")
	params.Set("language", "zh-CN")
	params.Set("browser_language", "zh-CN")
	params.Set("browser_platform", "Win32")
	params.Set("browser_name", "Chrome")
	params.Set("browser_version", "116.0.0.0")
	params.Set("web_rid", roomID)
	params.Set("msToken", "")

	ua := "Mozilla/5.0 (Windows NT 10.0; WOW64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/116.0.5845.97 Safari/537.36 Core/1.116.567.400 QQBrowser/19.7.6764.400"
	query := params.Encode()
	aBogus := generateABogus(query, ua)
	apiURL := fmt.Sprintf("https://live.douyin.com/webcast/room/web/enter/?%s&a_bogus=%s", query, aBogus)

	client := &http.Client{Timeout: 10 * time.Second}
	req, err := http.NewRequest("GET", apiURL, nil)
	if err != nil {
		return "", "", err
	}

	cookieMutex.RLock()
	myCookie := globalCookies.Douyin
	cookieMutex.RUnlock()

	req.Header.Set("User-Agent", ua)
	req.Header.Set("Accept-Language", "zh-CN,zh;q=0.8,zh-TW;q=0.7,zh-HK;q=0.5,en-US;q=0.3,en;q=0.2")
	req.Header.Set("Referer", "https://live.douyin.com/")
	if myCookie != "" {
		req.Header.Set("Cookie", myCookie)
	} else {
		req.Header.Set("Cookie", "ttwid=1%7C2iDIYVmjzMcpZ20fcaFde0VghXAA3NaNXE_SLR68IyE%7C1761045455%7Cab35197d5cfb21df6cbb2fa7ef1c9262206b062c315b9d04da746d0b37dfbc7d")
	}

	resp, err := client.Do(req)
	if err != nil {
		return "", "", err
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", "", err
	}

	var data struct {
		Data struct {
			Data []struct {
				Status    int `json:"status"`
				StreamURL struct {
					FlvPullURL    map[string]string `json:"flv_pull_url"`
					HlsPullURLMap map[string]string `json:"hls_pull_url_map"`
				} `json:"stream_url"`
			} `json:"data"`
			User struct {
				Nickname string `json:"nickname"`
			} `json:"user"`
		} `json:"data"`
	}

	json.Unmarshal(body, &data)
	if len(data.Data.Data) == 0 {
		return "", "", nil
	}

	roomData := data.Data.Data[0]
	anchorName := data.Data.User.Nickname
	if roomData.Status != 2 {
		return "", anchorName, nil
	}

	var streamURL string
	targetKey := "FULL_HD1"
	if quality == "hd" {
		targetKey = "HD1"
	} else if quality == "sd" {
		targetKey = "SD1"
	}

	streamURL = roomData.StreamURL.FlvPullURL[targetKey]
	if streamURL == "" {
		streamURL = roomData.StreamURL.HlsPullURLMap[targetKey]
	}
	if streamURL == "" {
		for _, v := range roomData.StreamURL.FlvPullURL {
			streamURL = v
			break
		}
	}
	return streamURL, anchorName, nil
}

// ==========================================
// 快手平台
// ==========================================

type KuaishouPlatform struct{}

func (k *KuaishouPlatform) GetPlatformName() string { return "Kuaishou" }
func (k *KuaishouPlatform) GetStreamURL(roomID string, quality string) (string, string, error) {
	reqURL := fmt.Sprintf("https://live.kuaishou.com/u/%s", roomID)
	client := &http.Client{Timeout: 10 * time.Second}
	req, err := http.NewRequest("GET", reqURL, nil)
	if err != nil {
		return "", "", err
	}

	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")
	cookieMutex.RLock()
	myCookie := globalCookies.Kuaishou
	cookieMutex.RUnlock()
	if myCookie != "" {
		req.Header.Set("Cookie", myCookie)
	} else {
		req.Header.Set("Cookie", "did=web_12345678901234567890123456789012")
	}

	resp, err := client.Do(req)
	if err != nil {
		return "", "", err
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", "", err
	}
	htmlStr := string(body)

	anchorName := roomID
	titleRe := regexp.MustCompile(`<title>([^<]+)</title>`)
	if m := titleRe.FindStringSubmatch(htmlStr); len(m) >= 2 {
		name := strings.Split(m[1], "在快手直播")[0]
		if strings.TrimSpace(name) != "" {
			anchorName = strings.TrimSpace(name)
		}
	}

	re := regexp.MustCompile(`window\.__INITIAL_STATE__=({.*?});\(function`)
	matches := re.FindSubmatch(body)
	if len(matches) < 2 {
		return "", anchorName, fmt.Errorf("无法获取快手数据")
	}

	streamRe := regexp.MustCompile(`"url":"([^"]+\.flv[^"]*)"`)
	streamMatches := streamRe.FindAllStringSubmatch(string(matches[1]), -1)
	if len(streamMatches) > 0 {
		idx := 0
		if quality == "sd" {
			idx = len(streamMatches) - 1
		}
		return strings.ReplaceAll(streamMatches[idx][1], `\u0026`, "&"), anchorName, nil
	}
	return "", anchorName, nil
}

// ==========================================
// Soop 平台
// ==========================================

type SoopPlatform struct{}

func (s *SoopPlatform) GetPlatformName() string { return "Soop" }
func (s *SoopPlatform) GetStreamURL(roomID string, quality string) (string, string, error) {
	apiURL := "https://live.afreecatv.com/afreeca/player_live_api.php"
	formData := url.Values{}
	formData.Set("bid", roomID)
	formData.Set("type", "live")
	formData.Set("player_type", "html5")

	client := &http.Client{Timeout: 10 * time.Second}
	req, err := http.NewRequest("POST", apiURL, strings.NewReader(formData.Encode()))
	if err != nil {
		return "", "", err
	}
	req.Header.Set("Content-Type", "application/x-www-form-urlencoded")
	req.Header.Set("User-Agent", "Mozilla/5.0")

	cookieMutex.RLock()
	if globalCookies.Soop != "" {
		req.Header.Set("Cookie", globalCookies.Soop)
	}
	cookieMutex.RUnlock()

	resp, err := client.Do(req)
	if err != nil {
		return "", "", err
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	var result map[string]interface{}
	json.Unmarshal(body, &result)

	channelInfo, ok := result["CHANNEL"].(map[string]interface{})
	if !ok {
		return "", roomID, nil
	}

	anchorName := roomID
	if n, ok := channelInfo["BJNICK"].(string); ok {
		anchorName = n
	}

	if res, ok := channelInfo["RESULT"].(float64); ok && res == 1 {
		if url, ok := channelInfo["CHDOMAIN"].(string); ok {
			return url, anchorName, nil
		}
	}
	return "", anchorName, nil
}

// ==========================================
// 录制控制逻辑
// ==========================================

func RecordStream(ctx context.Context, streamURL, platformName, roomID, anchorName, quality string, segmentTime int) {
	updateStatus(platformName, roomID, anchorName, quality, "录制中")
	safeName := sanitizeFileName(anchorName)
	if safeName == "" {
		safeName = roomID
	}

	// 动态获取全局配置中的保存路径，如果为空则默认使用 ./downloads
	baseDir := globalConfig.SavePath
	if baseDir == "" {
		baseDir = "./downloads"
	}

	outDir := filepath.Join(baseDir, safeName)
	os.MkdirAll(outDir, os.ModePerm)
	timestamp := time.Now().Format("2006-01-02_15-04-05")

	var args []string
	var outPath string

	if segmentTime > 0 {
		outPath = filepath.Join(outDir, fmt.Sprintf("%s_%s_%%03d.mp4", safeName, timestamp))
		args = []string{"-y", "-i", streamURL, "-c", "copy", "-f", "segment", "-segment_time", fmt.Sprintf("%d", segmentTime*60), "-reset_timestamps", "1", outPath}
	} else {
		outPath = filepath.Join(outDir, fmt.Sprintf("%s_%s.mp4", safeName, timestamp))
		args = []string{"-y", "-i", streamURL, "-c", "copy", "-f", "mp4", outPath}
	}

	log.Printf("\n🟢 [开始录制] 平台: %s | 主播: %s | 画质: %s\n   📂 路径: %s", platformName, anchorName, formatQualityName(quality), outPath)

	startTime := time.Now()
	cmd := exec.CommandContext(ctx, "ffmpeg", args...)
	cmd.Stdout = nil
	cmd.Stderr = nil
	err := cmd.Run()
	duration := time.Since(startTime)

	if err != nil {
		log.Printf("\n🔴 [录制结束] %s | %s | 时长: %s (异常/断流或已被手动暂停/删除)\n", platformName, anchorName, formatDuration(duration))
	} else {
		log.Printf("\n🔴 [录制结束] %s | %s | 时长: %s (完成)\n", platformName, anchorName, formatDuration(duration))
	}

	updateStatus(platformName, roomID, anchorName, quality, "未开播等待中")
}

func MonitorLive(p Platform, roomID string) {
	platformName := p.GetPlatformName()
	key := platformName + "_" + roomID

	taskStates.Store(key, "running")
	log.Printf("👀 [启动监控] %s 房间: %s", platformName, roomID)
	updateStatus(platformName, roomID, "", "-", "监控中")
	rand.Seed(time.Now().UnixNano())

	for {
		state, _ := taskStates.Load(key)

		if state == "deleted" {
			log.Printf("🗑️ [任务移除] 已停止监控 %s 房间: %s", platformName, roomID)
			globalStatus.Delete(key)
			activeTasks.Delete(key)
			return
		}

		if state == "paused" {
			updateStatus(platformName, roomID, "", "-", "已暂停")
			time.Sleep(2 * time.Second)
			continue
		}

		ctx, cancel := context.WithCancel(context.Background())
		activeCancels.Store(key, cancel)

		q := globalConfig.Quality
		st := globalConfig.SegmentTime

		url, name, err := p.GetStreamURL(roomID, q)
		if err != nil {
			log.Printf("⚠️ [检测出错] %s %s: %v", platformName, roomID, err)
		} else if url != "" {
			updateStatus(platformName, roomID, name, q, "录制中")
			RecordStream(ctx, url, platformName, roomID, name, q, st)

			state, _ = taskStates.Load(key)
			if state != "deleted" && state != "paused" {
				log.Printf("⏳ [断流等待] %s %s 进入15秒冷却...", platformName, name)
				updateStatus(platformName, roomID, name, q, "断流缓冲中")
				select {
				case <-ctx.Done():
				case <-time.After(15 * time.Second):
				}
			}
		} else {
			if name != "" {
				updateStatus(platformName, roomID, name, q, "监控中")
			}

			sleepDur := globalConfig.CheckInterval
			if sleepDur < 10 {
				sleepDur = 10
			}
			jitter := rand.Intn(5)

			updateStatus(platformName, roomID, name, q, "未开播等待中")

			select {
			case <-ctx.Done():
			case <-time.After(time.Duration(sleepDur+jitter) * time.Second):
			}
		}

		activeCancels.Delete(key)
		cancel()
	}
}

func startMonitorIfNotRunning(p Platform, roomID string) {
	key := p.GetPlatformName() + "_" + roomID
	if _, exists := activeTasks.Load(key); exists {
		return
	}
	activeTasks.Store(key, true)
	go MonitorLive(p, roomID)
}

func removeFromConfig(platform, roomID string) {
	remove := func(slice []string, val string) []string {
		var res []string
		for _, s := range slice {
			if s != val {
				res = append(res, s)
			}
		}
		return res
	}

	switch platform {
	case "Douyin":
		globalConfig.Douyin = remove(globalConfig.Douyin, roomID)
	case "Kuaishou":
		globalConfig.Kuaishou = remove(globalConfig.Kuaishou, roomID)
	case "Soop":
		globalConfig.Soop = remove(globalConfig.Soop, roomID)
	}

	data, _ := json.MarshalIndent(globalConfig, "", "    ")
	os.WriteFile("config.json", data, 0644)
}

// ==========================================
// Web 路由与主入口
// ==========================================

func handleIndex(w http.ResponseWriter, r *http.Request) {
	if _, err := os.Stat("index.html"); os.IsNotExist(err) {
		w.Write([]byte("Missing index.html"))
		return
	}
	http.ServeFile(w, r, "index.html")
}

func apiConfig(w http.ResponseWriter, r *http.Request) {
	if r.Method == "POST" {
		var c Config
		json.NewDecoder(r.Body).Decode(&c)
		if c.Quality != "" {
			globalConfig.Quality = c.Quality
		}
		globalConfig.SegmentTime = c.SegmentTime
		if c.SavePath != "" {
			globalConfig.SavePath = c.SavePath
		}
		data, _ := json.MarshalIndent(globalConfig, "", "    ")
		os.WriteFile("config.json", data, 0644)
	}
	json.NewEncoder(w).Encode(globalConfig)
}

func apiCookies(w http.ResponseWriter, r *http.Request) {
	if r.Method == "POST" {
		var c CookieConfig
		json.NewDecoder(r.Body).Decode(&c)
		cookieMutex.Lock()
		globalCookies.Douyin = c.Douyin
		globalCookies.Kuaishou = c.Kuaishou
		globalCookies.Soop = c.Soop
		cookieMutex.Unlock()
		data, _ := json.MarshalIndent(globalCookies, "", "    ")
		os.WriteFile("cookies.json", data, 0644)
	}
	cookieMutex.RLock()
	json.NewEncoder(w).Encode(globalCookies)
	cookieMutex.RUnlock()
}

// 动态计算 "录制时长" 和 "本地文件夹占用大小"
func apiStatus(w http.ResponseWriter, r *http.Request) {
	var list []TaskStatus
	globalStatus.Range(func(key, value interface{}) bool {
		task := *value.(*TaskStatus) // 拷贝一份当前状态

		// 1. 动态计算本次录制时长
		if task.Status == "录制中" && !task.startTime.IsZero() {
			task.Duration = formatDuration(time.Since(task.startTime))
		} else {
			task.Duration = "-"
		}

		// 2. 动态计算本地主播文件夹总大小（根据自定义路径）
		safeName := sanitizeFileName(task.AnchorName)
		if safeName == "" {
			safeName = task.RoomID
		}
		baseDir := globalConfig.SavePath
		if baseDir == "" {
			baseDir = "./downloads"
		}
		targetDir := filepath.Join(baseDir, safeName)
		task.FileSize = getDirSizeStr(targetDir)

		list = append(list, task)
		return true
	})
	json.NewEncoder(w).Encode(list)
}

func apiAdd(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		return
	}
	var d struct{ Platform, URL string }
	json.NewDecoder(r.Body).Decode(&d)
	roomID := extractRoomID(d.URL)
	var p Platform
	switch d.Platform {
	case "Douyin":
		globalConfig.Douyin = append(globalConfig.Douyin, roomID)
		p = &DouyinPlatform{}
	case "Kuaishou":
		globalConfig.Kuaishou = append(globalConfig.Kuaishou, roomID)
		p = &KuaishouPlatform{}
	case "Soop":
		globalConfig.Soop = append(globalConfig.Soop, roomID)
		p = &SoopPlatform{}
	}
	data, _ := json.MarshalIndent(globalConfig, "", "    ")
	os.WriteFile("config.json", data, 0644)
	startMonitorIfNotRunning(p, roomID)
	w.Write([]byte(`{"code":0}`))
}

func apiControl(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		return
	}
	var req struct {
		Action   string `json:"action"`
		Platform string `json:"platform"`
		RoomID   string `json:"room_id"`
	}
	json.NewDecoder(r.Body).Decode(&req)

	key := req.Platform + "_" + req.RoomID

	switch req.Action {
	case "pause":
		taskStates.Store(key, "paused")
		if cancel, ok := activeCancels.Load(key); ok {
			cancel.(context.CancelFunc)()
		}
	case "resume":
		taskStates.Store(key, "running")
	case "delete":
		taskStates.Store(key, "deleted")
		if cancel, ok := activeCancels.Load(key); ok {
			cancel.(context.CancelFunc)()
		}
		removeFromConfig(req.Platform, req.RoomID)
	}

	w.Write([]byte(`{"code":0}`))
}

func main() {
	checkFFmpeg()

	if _, err := os.Stat("config.json"); os.IsNotExist(err) {
		globalConfig = &Config{Quality: "uhd", CheckInterval: 30, SavePath: "./downloads"}
		d, _ := json.MarshalIndent(globalConfig, "", "    ")
		os.WriteFile("config.json", d, 0644)
	} else {
		d, _ := os.ReadFile("config.json")
		globalConfig = &Config{}
		json.Unmarshal(d, globalConfig)
	}
	if globalConfig.CheckInterval == 0 {
		globalConfig.CheckInterval = 30
	}
	if globalConfig.SavePath == "" {
		globalConfig.SavePath = "./downloads"
	}

	if _, err := os.Stat("cookies.json"); os.IsNotExist(err) {
		globalCookies = &CookieConfig{}
		d, _ := json.MarshalIndent(globalCookies, "", "    ")
		os.WriteFile("cookies.json", d, 0644)
	} else {
		d, _ := os.ReadFile("cookies.json")
		globalCookies = &CookieConfig{}
		json.Unmarshal(d, globalCookies)
	}

	douyin := &DouyinPlatform{}
	kuaishou := &KuaishouPlatform{}
	soop := &SoopPlatform{}

	for _, id := range globalConfig.Douyin {
		startMonitorIfNotRunning(douyin, extractRoomID(id))
	}
	for _, id := range globalConfig.Kuaishou {
		startMonitorIfNotRunning(kuaishou, extractRoomID(id))
	}
	for _, id := range globalConfig.Soop {
		startMonitorIfNotRunning(soop, extractRoomID(id))
	}

	log.Println("🚀 服务已启动，监听端口 9091")
	log.Println("👉 内网访问地址: http://192.168.5.10:9091")

	http.HandleFunc("/", handleIndex)
	http.HandleFunc("/api/config", apiConfig)
	http.HandleFunc("/api/cookies", apiCookies)
	http.HandleFunc("/api/status", apiStatus)
	http.HandleFunc("/api/add", apiAdd)
	http.HandleFunc("/api/control", apiControl)

	if err := http.ListenAndServe(":8080", nil); err != nil {
		log.Fatalf("Web服务启动失败: %v", err)
	}
}
