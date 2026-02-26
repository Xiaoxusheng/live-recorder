package main

import (
	"context"
	_ "embed"
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
	"os/signal"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
	"syscall"
	"time"
)

// ==========================================
// 核心升级：打包静态资源
// ==========================================

//go:embed index.html
var indexHtml []byte // ✨ 魔法发生在这里：编译时会将 index.html 的内容自动塞入这个变量

// 全局 ffmpeg 路径变量
var ffmpegPath string = "ffmpeg"

// ==========================================
// 核心优化 1：全局 HTTP 连接池复用
// ==========================================
var globalHTTPClient = &http.Client{
	Timeout: 30 * time.Second, // 应对某些节点响应慢的情况
	Transport: &http.Transport{
		MaxIdleConns:        100,
		MaxIdleConnsPerHost: 20,
		IdleConnTimeout:     90 * time.Second,
		DisableKeepAlives:   false, // 允许连接复用
	},
}

// ==========================================
// 全局状态与结构定义
// ==========================================

type TaskStatus struct {
	Platform   string `json:"platform"`
	RoomID     string `json:"room_id"`
	AnchorName string `json:"anchor_name"`
	Avatar     string `json:"avatar"` // 新增字段：用于在前端显示真实的头像图片
	Quality    string `json:"quality"`
	Status     string `json:"status"`
	UpdateTime string `json:"update_time"`
	IsPaused   bool   `json:"is_paused"`
	FileSize   string `json:"file_size"`
	Duration   string `json:"duration"`

	startTime time.Time `json:"-"`
}

var (
	globalConfig  *Config
	activeTasks   sync.Map
	globalStatus  sync.Map
	globalCookies *CookieConfig
	cookieMutex   sync.RWMutex

	taskStates        sync.Map // key: platform_roomID, value: "running", "paused", "deleted"
	activeCancels     sync.Map // key: platform_roomID, value: context.CancelFunc
	globalCustomNames sync.Map // 内存中保存的自定义名称 (由 txt 提供)
)

func updateStatus(platform, roomID, anchorName, avatar, quality, statusMsg string) {
	key := platform + "_" + roomID
	now := time.Now()
	var sTime time.Time

	if existing, ok := globalStatus.Load(key); ok {
		oldTask := existing.(*TaskStatus)
		if anchorName == "" {
			anchorName = oldTask.AnchorName
		}
		if avatar == "" {
			avatar = oldTask.Avatar
		}
		if statusMsg == "录制中" {
			if oldTask.Status != "录制中" {
				sTime = now
			} else {
				sTime = oldTask.startTime
			}
		}
	} else {
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
		Avatar:     avatar, // 保存头像
		Quality:    quality,
		Status:     statusMsg,
		UpdateTime: time.Now().Format("2006-01-02 15:04:05"),
		IsPaused:   isPaused,
		startTime:  sTime,
	})
}

// Config 已经移除了所有 Json 主播列表相关的字段，完全依赖 urls.txt
type Config struct {
	Quality       string `json:"quality"`
	SegmentTime   int    `json:"segment_time"`
	CheckInterval int    `json:"check_interval"`
	SavePath      string `json:"save_path"`
}

// 临时结构体：用于把老旧版本的 Json 数据平滑迁移到 urls.txt
type OldConfig struct {
	Douyin      []string          `json:"douyin"`
	Kuaishou    []string          `json:"kuaishou"`
	Soop        []string          `json:"soop"`
	PausedTasks []string          `json:"paused_tasks"`
	CustomNames map[string]string `json:"custom_names"`
}

type CookieConfig struct {
	Douyin   string `json:"douyin"`
	Kuaishou string `json:"kuaishou"`
	Soop     string `json:"soop"`
}

type Platform interface {
	GetPlatformName() string
	GetStreamURL(roomID string, quality string) (streamURL string, anchorName string, avatar string, err error)
}

func saveConfig() {
	data, _ := json.MarshalIndent(globalConfig, "", "    ")
	os.WriteFile("config.json", data, 0644)
}

// ==========================================
// 文本存储同步核心逻辑 (urls.txt)
// ==========================================

var anchorLinesMutex sync.Mutex

// 同步状态到 txt 文本
func syncAnchorToTxt(action string, platform, roomID string, rawLine string) {
	anchorLinesMutex.Lock()
	defer anchorLinesMutex.Unlock()

	content, err := os.ReadFile("urls.txt")
	var lines []string
	if err == nil {
		lines = strings.Split(string(content), "\n")
	}

	var newLines []string
	found := false

	for _, line := range lines {
		trimmed := strings.TrimSpace(line)
		if trimmed == "" {
			continue
		}

		isP, p, rid, _, _ := parseLine(trimmed)
		if p == platform && rid == roomID {
			found = true
			if action == "delete" {
				continue // 丢弃这一行
			} else if action == "pause" {
				if !isP {
					newLines = append(newLines, "#"+trimmed)
				} else {
					newLines = append(newLines, trimmed)
				}
			} else if action == "resume" {
				if isP {
					newLines = append(newLines, strings.TrimSpace(strings.TrimPrefix(trimmed, "#")))
				} else {
					newLines = append(newLines, trimmed)
				}
			}
		} else {
			newLines = append(newLines, trimmed)
		}
	}

	if !found && action == "add" && rawLine != "" {
		newLines = append(newLines, strings.TrimSpace(rawLine))
	}

	os.WriteFile("urls.txt", []byte(strings.Join(newLines, "\n")+"\n"), 0644)
}

// 智能解析单行文本
func parseLine(line string) (isPaused bool, platform string, roomID string, customName string, rawURL string) {
	line = strings.TrimSpace(line)
	if line == "" {
		return
	}

	if strings.HasPrefix(line, "#") {
		isPaused = true
		line = strings.TrimSpace(strings.TrimPrefix(line, "#"))
	}

	// 提取自定义名字
	if idx := strings.Index(line, ",主播:"); idx != -1 {
		customName = strings.TrimSpace(line[idx+len(",主播:"):])
		rawURL = strings.TrimSpace(line[:idx])
	} else if idx := strings.Index(line, ", 主播:"); idx != -1 {
		customName = strings.TrimSpace(line[idx+len(", 主播:"):])
		rawURL = strings.TrimSpace(line[:idx])
	} else if idx := strings.Index(line, ","); idx != -1 {
		customName = strings.TrimSpace(line[idx+1:])
		rawURL = strings.TrimSpace(line[:idx])
	} else {
		rawURL = line
	}

	// 识别平台
	if strings.Contains(rawURL, "douyin.com") {
		platform = "Douyin"
	} else if strings.Contains(rawURL, "kuaishou.com") {
		platform = "Kuaishou"
	} else if strings.Contains(rawURL, "sooplive.co.kr") || strings.Contains(rawURL, "afreecatv.com") {
		platform = "Soop"
	}

	roomID = extractRoomID(rawURL)
	return
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
	localPath := filepath.Join(".", "ffmpeg.exe")
	if _, err := os.Stat(localPath); err == nil {
		absPath, _ := filepath.Abs(localPath)
		ffmpegPath = absPath
		log.Println("✅ 成功加载本地 ffmpeg:", ffmpegPath)
		return
	}
	path, err := exec.LookPath("ffmpeg")
	if err == nil {
		ffmpegPath = path
		log.Println("✅ 成功加载系统 ffmpeg:", ffmpegPath)
		return
	}
	log.Println("❌ 【错误】未找到 ffmpeg！请将 ffmpeg.exe 放入程序同级目录！")
}

func extractRoomID(input string) string {
	input = strings.TrimSpace(input)
	if strings.HasPrefix(input, "http://") || strings.HasPrefix(input, "https://") {
		u, err := url.Parse(input)
		if err == nil {
			path := strings.Trim(u.Path, "/")
			segments := strings.Split(path, "/")

			if strings.Contains(u.Host, "sooplive.co.kr") || strings.Contains(u.Host, "afreecatv.com") {
				if len(segments) > 0 {
					return segments[0]
				}
			}

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
// 抖音平台实现部分
// ==========================================

type DouyinPlatform struct{}

func (d *DouyinPlatform) GetPlatformName() string { return "Douyin" }

func (d *DouyinPlatform) GetStreamURL(roomID string, quality string) (string, string, string, error) {
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

	req, err := http.NewRequest("GET", apiURL, nil)
	if err != nil {
		return "", "", "", err
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

	resp, err := globalHTTPClient.Do(req)
	if err != nil {
		return "", "", "", err
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", "", "", err
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
				Nickname    string `json:"nickname"`
				AvatarThumb struct {
					UrlList []string `json:"url_list"` // 新增：提取头像
				} `json:"avatar_thumb"`
			} `json:"user"`
		} `json:"data"`
	}

	json.Unmarshal(body, &data)
	if len(data.Data.Data) == 0 {
		return "", "", "", nil
	}

	roomData := data.Data.Data[0]
	anchorName := data.Data.User.Nickname

	avatar := ""
	if len(data.Data.User.AvatarThumb.UrlList) > 0 {
		avatar = data.Data.User.AvatarThumb.UrlList[0]
	}

	if roomData.Status != 2 {
		return "", anchorName, avatar, nil
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
	return streamURL, anchorName, avatar, nil
}

// ==========================================
// 快手平台
// ==========================================

type KuaishouPlatform struct{}

func (k *KuaishouPlatform) GetPlatformName() string { return "Kuaishou" }
func (k *KuaishouPlatform) GetStreamURL(roomID string, quality string) (string, string, string, error) {
	reqURL := fmt.Sprintf("https://live.kuaishou.com/u/%s", roomID)
	req, err := http.NewRequest("GET", reqURL, nil)
	if err != nil {
		return "", "", "", err
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

	resp, err := globalHTTPClient.Do(req)
	if err != nil {
		return "", "", "", err
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", "", "", err
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

	avatar := ""
	avatarRe := regexp.MustCompile(`"headUrl":"([^"]+)"`)
	if m := avatarRe.FindStringSubmatch(htmlStr); len(m) >= 2 {
		avatar = strings.ReplaceAll(m[1], `\u002F`, "/")
	} else {
		avatarRe2 := regexp.MustCompile(`"avatar":"([^"]+)"`)
		if m2 := avatarRe2.FindStringSubmatch(htmlStr); len(m2) >= 2 {
			avatar = strings.ReplaceAll(m2[1], `\u002F`, "/")
		}
	}

	re := regexp.MustCompile(`window\.__INITIAL_STATE__=({.*?});\(function`)
	matches := re.FindSubmatch(body)
	if len(matches) < 2 {
		return "", anchorName, avatar, fmt.Errorf("无法获取快手数据")
	}

	streamRe := regexp.MustCompile(`"url":"([^"]+\.flv[^"]*)"`)
	streamMatches := streamRe.FindAllStringSubmatch(string(matches[1]), -1)
	if len(streamMatches) > 0 {
		idx := 0
		if quality == "sd" {
			idx = len(streamMatches) - 1
		}
		return strings.ReplaceAll(streamMatches[idx][1], `\u0026`, "&"), anchorName, avatar, nil
	}
	return "", anchorName, avatar, nil
}

// ==========================================
// Soop 平台
// ==========================================

type SoopPlatform struct{}

func (s *SoopPlatform) GetPlatformName() string { return "Soop" }

func (s *SoopPlatform) GetStreamURL(roomID string, quality string) (string, string, string, error) {
	apiURL := "http://api.m.sooplive.co.kr/broad/a/watch"
	formData := url.Values{}
	formData.Set("bj_id", roomID)
	formData.Set("broad_no", "")
	formData.Set("agent", "web")
	formData.Set("confirm_adult", "true")
	formData.Set("player_type", "webm")
	formData.Set("mode", "live")

	req, err := http.NewRequest("POST", apiURL, strings.NewReader(formData.Encode()))
	if err != nil {
		return "", roomID, "", err
	}

	req.Header.Set("Content-Type", "application/x-www-form-urlencoded")
	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:109.0) Gecko/20100101 Firefox/119.0")
	req.Header.Set("Origin", "https://m.sooplive.co.kr")
	req.Header.Set("Referer", "https://m.sooplive.co.kr/")
	req.Header.Set("Accept-Language", "zh-CN,zh;q=0.8,zh-TW;q=0.7,zh-HK;q=0.5,en-US;q=0.3,en;q=0.2")

	cookieMutex.RLock()
	if globalCookies.Soop != "" {
		req.Header.Set("Cookie", globalCookies.Soop)
	}
	cookieMutex.RUnlock()

	resp, err := globalHTTPClient.Do(req)
	if err != nil {
		return "", roomID, "", err
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", roomID, "", err
	}

	var result map[string]interface{}
	if err := json.Unmarshal(body, &result); err != nil {
		return "", roomID, "", fmt.Errorf("JSON 解析失败: %v", err)
	}

	dataMap, _ := result["data"].(map[string]interface{})

	anchorName := roomID
	if dataMap != nil {
		if nick, ok := dataMap["user_nick"].(string); ok && nick != "" {
			if bjID, ok := dataMap["bj_id"].(string); ok && bjID != "" {
				anchorName = fmt.Sprintf("%s-%s", nick, bjID)
			} else {
				anchorName = nick
			}
		}
	}

	resCode, ok := result["result"].(float64)
	if !ok || resCode != 1 {
		if dataMap != nil {
			if code, ok := dataMap["code"].(float64); ok {
				if code == -6001 {
					return "", anchorName, "", nil
				} else if code == -3001 {
					return "", anchorName, "", nil
				} else if code == -3002 || code == -3004 {
					return "", anchorName, "", fmt.Errorf("该直播需要19+登录或验证，请在配置中提供对应 Cookie (code: %v)", code)
				}
			}
		}
		return "", anchorName, "", fmt.Errorf("未知异常或开播请求失败")
	}

	avatar := ""
	if dataMap != nil {
		if bjID, ok := dataMap["bj_id"].(string); ok && len(bjID) >= 2 {
			avatar = fmt.Sprintf("https://stimg.afreecatv.com/LOGO/%s/%s/%s.jpg", bjID[:2], bjID, bjID)
		}
	}

	broadNoStr := ""
	if bn, ok := dataMap["broad_no"].(string); ok {
		broadNoStr = bn
	} else if bnFloat, ok := dataMap["broad_no"].(float64); ok {
		broadNoStr = fmt.Sprintf("%.0f", bnFloat)
	}

	aid := ""
	if a, ok := dataMap["hls_authentication_key"].(string); ok {
		aid = a
	}

	if broadNoStr == "" || aid == "" {
		return "", anchorName, avatar, fmt.Errorf("提取 broad_no 或 aid 失败")
	}

	cdnURL := fmt.Sprintf("http://livestream-manager.sooplive.co.kr/broad_stream_assign.html?return_type=gcp_cdn&use_cors=false&cors_origin_url=play.sooplive.co.kr&broad_key=%s-common-master-hls&time=8361.086329376785", broadNoStr)

	reqCdn, err := http.NewRequest("GET", cdnURL, nil)
	if err != nil {
		return "", anchorName, avatar, err
	}

	reqCdn.Header.Set("User-Agent", "Mozilla/5.0")
	reqCdn.Header.Set("Origin", "https://play.sooplive.co.kr")
	reqCdn.Header.Set("Referer", "https://play.sooplive.co.kr/")
	reqCdn.Header.Set("Content-Type", "application/x-www-form-urlencoded")

	respCdn, err := globalHTTPClient.Do(reqCdn)
	if err != nil {
		return "", anchorName, avatar, err
	}
	defer respCdn.Body.Close()

	bodyCdn, err := io.ReadAll(respCdn.Body)
	if err != nil {
		return "", anchorName, avatar, err
	}

	var cdnResult map[string]interface{}
	if err := json.Unmarshal(bodyCdn, &cdnResult); err != nil {
		return "", anchorName, avatar, fmt.Errorf("CDN响应 JSON 解析失败: %v", err)
	}

	viewURL, ok := cdnResult["view_url"].(string)
	if !ok || viewURL == "" {
		return "", anchorName, avatar, fmt.Errorf("从 CDN 节点提取 view_url 失败")
	}

	finalStreamURL := fmt.Sprintf("%s?aid=%s", viewURL, aid)

	return finalStreamURL, anchorName, avatar, nil
}

// ==========================================
// 录制流逻辑
// ==========================================

func RecordStream(ctx context.Context, streamURL, platformName, roomID, anchorName, avatar, quality string, segmentTime int) {
	updateStatus(platformName, roomID, anchorName, avatar, quality, "录制中")
	safeName := sanitizeFileName(anchorName)
	if safeName == "" {
		safeName = roomID
	}

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
		args = []string{"-y", "-analyzeduration", "2000000", "-probesize", "2000000", "-i", streamURL, "-c", "copy", "-f", "segment", "-segment_time", fmt.Sprintf("%d", segmentTime*60), "-reset_timestamps", "1", "-movflags", "frag_keyframe+empty_moov", outPath}
	} else {
		outPath = filepath.Join(outDir, fmt.Sprintf("%s_%s.mp4", safeName, timestamp))
		args = []string{"-y", "-analyzeduration", "2000000", "-probesize", "2000000", "-i", streamURL, "-c", "copy", "-f", "mp4", "-movflags", "frag_keyframe+empty_moov", outPath}
	}

	log.Printf("\n🟢 [开始录制] 平台: %s | 主播: %s | 画质: %s\n   📂 路径: %s", platformName, anchorName, formatQualityName(quality), outPath)

	startTime := time.Now()

	cmd := exec.Command(ffmpegPath, args...)

	stdin, err := cmd.StdinPipe()
	if err != nil {
		log.Printf("获取ffmpeg stdin失败: %v", err)
		return
	}

	cmd.Stdout = nil
	cmd.Stderr = nil

	if err := cmd.Start(); err != nil {
		log.Printf("\n🔴 [启动录制失败] %s | %s: %v\n", platformName, anchorName, err)
		updateStatus(platformName, roomID, anchorName, avatar, quality, "未开播等待中")
		return
	}

	done := make(chan error, 1)
	go func() {
		done <- cmd.Wait()
	}()

	select {
	case <-ctx.Done():
		if stdin != nil {
			io.WriteString(stdin, "q\n")
			stdin.Close()
		}

		select {
		case <-done:
			log.Printf("\n🔴 [手动停止] %s | %s | 录像已安全保存完毕\n", platformName, anchorName)
		case <-time.After(10 * time.Second):
			cmd.Process.Kill()
			log.Printf("\n🔴 [手动停止超时强杀] %s | %s\n", platformName, anchorName)
		}
	case err := <-done:
		duration := time.Since(startTime)
		if err != nil {
			log.Printf("\n🔴 [录制异常/断流] %s | %s | 时长: %s\n", platformName, anchorName, formatDuration(duration))
		} else {
			log.Printf("\n🔴 [录制结束] %s | %s | 时长: %s (自然完成)\n", platformName, anchorName, formatDuration(duration))
		}
	}

	updateStatus(platformName, roomID, anchorName, avatar, quality, "未开播等待中")
}

func MonitorLive(p Platform, roomID string) {
	platformName := p.GetPlatformName()
	key := platformName + "_" + roomID

	// 此处保持为空，稍后会在循环中通过 txt 记忆的数据覆盖
	taskStates.Store(key, "running")
	log.Printf("👀 [启动监控] %s 房间: %s", platformName, roomID)
	updateStatus(platformName, roomID, "", "", "-", "监控中")

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
			updateStatus(platformName, roomID, "", "", "-", "已暂停")
			time.Sleep(2 * time.Second)
			continue
		}

		ctx, cancel := context.WithCancel(context.Background())
		activeCancels.Store(key, cancel)

		q := globalConfig.Quality
		st := globalConfig.SegmentTime

		url, name, avatar, err := p.GetStreamURL(roomID, q)

		if custom, ok := globalCustomNames.Load(key); ok && custom.(string) != "" {
			name = custom.(string)
		}

		if err != nil {
			log.Printf("⚠️ [检测出错] %s %s: %v", platformName, roomID, err)
			updateStatus(platformName, roomID, name, avatar, q, "检测异常等待中")

			sleepDur := globalConfig.CheckInterval
			if sleepDur < 10 {
				sleepDur = 10
			}
			t := time.NewTimer(time.Duration(sleepDur) * time.Second)
			select {
			case <-ctx.Done():
				t.Stop()
			case <-t.C:
			}
		} else if url != "" {
			updateStatus(platformName, roomID, name, avatar, q, "录制中")
			RecordStream(ctx, url, platformName, roomID, name, avatar, q, st)

			state, _ = taskStates.Load(key)
			if state != "deleted" && state != "paused" {
				log.Printf("⏳ [断流等待] %s %s 进入15秒冷却...", platformName, name)
				updateStatus(platformName, roomID, name, avatar, q, "断流缓冲中")

				t := time.NewTimer(15 * time.Second)
				select {
				case <-ctx.Done():
					t.Stop()
				case <-t.C:
				}
			}
		} else {
			if name == "" {
				if custom, ok := globalCustomNames.Load(key); ok && custom.(string) != "" {
					name = custom.(string)
				}
			}
			if name != "" {
				updateStatus(platformName, roomID, name, avatar, q, "监控中")
			}

			sleepDur := globalConfig.CheckInterval
			if sleepDur < 10 {
				sleepDur = 10
			}
			jitter := rand.Intn(5)

			updateStatus(platformName, roomID, name, avatar, q, "未开播等待中")

			t := time.NewTimer(time.Duration(sleepDur+jitter) * time.Second)
			select {
			case <-ctx.Done():
				t.Stop()
			case <-t.C:
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

// ==========================================
// Web 路由与主入口
// ==========================================

func handleIndex(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Cache-Control", "no-cache, no-store, must-revalidate")
	w.Header().Set("Pragma", "no-cache")
	w.Header().Set("Expires", "0")
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	w.Write(indexHtml)
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
		saveConfig()
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

func apiStatus(w http.ResponseWriter, r *http.Request) {
	var list []TaskStatus
	globalStatus.Range(func(key, value interface{}) bool {
		task := *value.(*TaskStatus)

		if task.Status == "录制中" && !task.startTime.IsZero() {
			task.Duration = formatDuration(time.Since(task.startTime))
		} else {
			task.Duration = "-"
		}

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

	// 后端支持解析文本框传来的大量行
	lines := strings.Split(d.URL, "\n")

	for _, line := range lines {
		line = strings.TrimSpace(line)

		if line == "" || strings.HasPrefix(line, "//") {
			continue
		}

		isP, platformName, roomID, customName, rawURL := parseLine(line)

		if roomID == "" {
			continue
		}

		// 容错：如果解析不出平台，就用前端传来的兜底平台
		if platformName == "" {
			platformName = d.Platform
		}

		key := platformName + "_" + roomID

		if customName != "" {
			globalCustomNames.Store(key, customName)
		}

		// 如果内存中已存在此任务，忽略它
		if _, exists := activeTasks.Load(key); exists {
			continue
		}
		if _, exists := globalStatus.Load(key); exists {
			continue
		}

		var p Platform
		switch platformName {
		case "Douyin":
			p = &DouyinPlatform{}
		case "Kuaishou":
			p = &KuaishouPlatform{}
		case "Soop":
			p = &SoopPlatform{}
		default:
			continue
		}

		// 同步存入 urls.txt 文件
		syncAnchorToTxt("add", platformName, roomID, rawURL)

		displayName := customName
		if displayName == "" {
			displayName = roomID
		}

		if isP {
			taskStates.Store(key, "paused")
			updateStatus(platformName, roomID, displayName, "", globalConfig.Quality, "已暂停")
		} else {
			updateStatus(platformName, roomID, displayName, "", globalConfig.Quality, "初始化中")
			startMonitorIfNotRunning(p, roomID)
		}
	}

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
		syncAnchorToTxt("pause", req.Platform, req.RoomID, "")

	case "resume":
		taskStates.Store(key, "running")
		syncAnchorToTxt("resume", req.Platform, req.RoomID, "")

	case "delete":
		taskStates.Store(key, "deleted")
		if cancel, ok := activeCancels.Load(key); ok {
			cancel.(context.CancelFunc)()
		}
		syncAnchorToTxt("delete", req.Platform, req.RoomID, "")
		globalStatus.Delete(key) // 立即在前端移除
		activeTasks.Delete(key)
	}

	w.Write([]byte(`{"code":0}`))
}

func main() {
	checkFFmpeg()

	// 1. 读取基础设置 config.json
	if _, err := os.Stat("config.json"); os.IsNotExist(err) {
		globalConfig = &Config{Quality: "uhd", CheckInterval: 30, SavePath: "./downloads"}
		saveConfig()
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

	// 平滑过度旧版本数据到 urls.txt
	if _, err := os.Stat("urls.txt"); os.IsNotExist(err) {
		d, err2 := os.ReadFile("config.json")
		if err2 == nil {
			var oldConf OldConfig
			json.Unmarshal(d, &oldConf)
			var lines []string

			for _, id := range oldConf.Douyin {
				isP := false
				for _, p := range oldConf.PausedTasks {
					if p == "Douyin_"+id {
						isP = true
					}
				}
				name := oldConf.CustomNames["Douyin_"+id]
				prefix := ""
				if isP {
					prefix = "#"
				}
				suffix := ""
				if name != "" {
					suffix = ",主播: " + name
				}
				lines = append(lines, fmt.Sprintf("%shttps://live.douyin.com/%s%s", prefix, id, suffix))
			}
			for _, id := range oldConf.Kuaishou {
				isP := false
				for _, p := range oldConf.PausedTasks {
					if p == "Kuaishou_"+id {
						isP = true
					}
				}
				name := oldConf.CustomNames["Kuaishou_"+id]
				prefix := ""
				if isP {
					prefix = "#"
				}
				suffix := ""
				if name != "" {
					suffix = ",主播: " + name
				}
				lines = append(lines, fmt.Sprintf("%shttps://live.kuaishou.com/u/%s%s", prefix, id, suffix))
			}
			for _, id := range oldConf.Soop {
				isP := false
				for _, p := range oldConf.PausedTasks {
					if p == "Soop_"+id {
						isP = true
					}
				}
				name := oldConf.CustomNames["Soop_"+id]
				prefix := ""
				if isP {
					prefix = "#"
				}
				suffix := ""
				if name != "" {
					suffix = ",主播: " + name
				}
				lines = append(lines, fmt.Sprintf("%shttps://play.sooplive.co.kr/%s/0%s", prefix, id, suffix))
			}

			if len(lines) > 0 {
				os.WriteFile("urls.txt", []byte(strings.Join(lines, "\n")+"\n"), 0644)
				log.Println("✅ 成功将旧版 config.json 主播迁移至 urls.txt")
			}
		}
	}

	// 2. 读取 Cookie
	if _, err := os.Stat("cookies.json"); os.IsNotExist(err) {
		globalCookies = &CookieConfig{}
		d, _ := json.MarshalIndent(globalCookies, "", "    ")
		os.WriteFile("cookies.json", d, 0644)
	} else {
		d, _ := os.ReadFile("cookies.json")
		globalCookies = &CookieConfig{}
		json.Unmarshal(d, globalCookies)
	}

	// 3. 核心：从 urls.txt 启动任务！
	content, err := os.ReadFile("urls.txt")
	if err == nil {
		lines := strings.Split(string(content), "\n")
		for _, line := range lines {
			isPaused, platform, roomID, customName, _ := parseLine(line)

			if roomID == "" || platform == "" {
				continue
			}

			key := platform + "_" + roomID

			if customName != "" {
				globalCustomNames.Store(key, customName)
			}

			var p Platform
			switch platform {
			case "Douyin":
				p = &DouyinPlatform{}
			case "Kuaishou":
				p = &KuaishouPlatform{}
			case "Soop":
				p = &SoopPlatform{}
			default:
				continue
			}

			if isPaused {
				taskStates.Store(key, "paused")
				displayName := customName
				if displayName == "" {
					displayName = roomID
				}
				updateStatus(platform, roomID, displayName, "", globalConfig.Quality, "已暂停")
			} else {
				displayName := customName
				if displayName == "" {
					displayName = roomID
				}
				updateStatus(platform, roomID, displayName, "", globalConfig.Quality, "初始化中")
				startMonitorIfNotRunning(p, roomID)
			}
		}
	} else {
		// 如果不存在，创建空的 urls.txt
		os.WriteFile("urls.txt", []byte(""), 0644)
	}

	// 4. 信号拦截与优雅退出
	stopSignal := make(chan os.Signal, 1)
	signal.Notify(stopSignal, os.Interrupt, syscall.SIGTERM)
	go func() {
		<-stopSignal
		log.Println("\n⚠️ 收到系统退出/重启信号！正在通知所有录像安全收尾并保存，请稍候...")
		activeCancels.Range(func(key, value interface{}) bool {
			if cancel, ok := value.(context.CancelFunc); ok {
				cancel()
			}
			return true
		})
		time.Sleep(3 * time.Second)
		log.Println("✅ 所有视频均已安全保存！服务正式退出。")
		os.Exit(0)
	}()

	log.Println("🚀 服务已启动，监听端口 9091")
	log.Println("👉 请自行查看本机 IP 访问，或尝试: http://localhost:9091")

	http.HandleFunc("/", handleIndex)
	http.HandleFunc("/api/config", apiConfig)
	http.HandleFunc("/api/cookies", apiCookies)
	http.HandleFunc("/api/status", apiStatus)
	http.HandleFunc("/api/add", apiAdd)
	http.HandleFunc("/api/control", apiControl)

	if err := http.ListenAndServe(":9091", nil); err != nil {
		log.Fatalf("Web服务启动失败: %v", err)
	}
}
