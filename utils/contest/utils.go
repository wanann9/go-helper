package contest

import (
	"container/list"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"sort"
	"strconv"
	"strings"

	"github.com/emirpasic/gods/sets/hashset"
	"github.com/emirpasic/gods/trees/binaryheap"
	"github.com/emirpasic/gods/trees/redblacktree"
	"github.com/emirpasic/gods/utils"
)

var prt, prf = fmt.Println, fmt.Printf

var s2i = func(s string, base int) int {
	rst, _ := strconv.ParseInt(s, base, 64)
	return int(rst)
}

var i2s = func(i, base int) string {
	return strconv.FormatInt(int64(i), base)
}

var b2i = func(b bool) int {
	if b {
		return 1
	}
	return 0
}

var isNumber = func(c byte) bool {
	return c >= '0' && c <= '9'
}

var isLetter = func(c byte) bool {
	return isLower(c) || isUpper(c)
}

var isLower = func(c byte) bool {
	return c >= 'a' && c <= 'z'
}

var isUpper = func(c byte) bool {
	return c >= 'A' && c <= 'Z'
}

var toLower = func(c byte) byte {
	if isUpper(c) {
		return c ^ 32
	}
	return c
}

var toUpper = func(c byte) byte {
	if isLower(c) {
		return c ^ 32
	}
	return c
}

var abs = func(a int) int {
	if a >= 0 {
		return a
	}
	return -a
}

var min = func(nums ...int) int {
	rst := math.MaxInt
	for _, n := range nums {
		if n < rst {
			rst = n
		}
	}
	return rst
}

var max = func(nums ...int) int {
	rst := math.MinInt
	for _, n := range nums {
		if n > rst {
			rst = n
		}
	}
	return rst
}

var pow = func(a, b, mod int) (rst int) {
	for rst = 1; b > 0; b >>= 1 {
		if b&1 != 0 {
			if rst *= a; mod > 1 {
				rst %= mod
			}
		}
		if a *= a; mod > 1 {
			a %= mod
		}
	}
	return
}

func gcd(a, b int) int {
	if a%b == 0 {
		return b
	}
	return gcd(b, a%b)
}

var lcm = func(a, b int) int {
	return a / gcd(a, b) * b
}

var c [][]int

func _initC(n, mod int) {
	c = mtx(n+1, n+1, 0)
	for i := 0; i <= n; i++ {
		c[i][0] = 1
		for j := 1; j <= i; j++ {
			if c[i][j] = c[i-1][j-1] + c[i-1][j]; mod > 1 {
				c[i][j] %= mod
			}
		}
	}
}

var isPrime = func(n int) bool {
	if n <= 1 {
		return false
	}
	for i := 2; i*i <= n; i++ {
		if n%i == 0 {
			return false
		}
	}
	return true
}

var factor = func(n int) map[int]int {
	rst := make(map[int]int)
	for i := 2; i*i <= n; i++ {
		for ; n%i == 0; n /= i {
			rst[i]++
		}
	}
	if n > 1 {
		rst[n]++
	}
	return rst
}

var vct = func(l, init int) []int {
	v := make([]int, l)
	if init != 0 {
		for i := range v {
			v[i] = init
		}
	}
	return v
}

var mtx = func(l1, l2, init int) [][]int {
	m := make([][]int, l1)
	for i := range m {
		m[i] = vct(l2, init)
	}
	return m
}

var cb = func(l1, l2, l3, init int) [][][]int {
	c := make([][][]int, l1)
	for i := range c {
		c[i] = mtx(l2, l3, init)
	}
	return c
}

var vctBool = func(l int, init bool) []bool {
	v := make([]bool, l)
	if init {
		for i := range v {
			v[i] = true
		}
	}
	return v
}

var mtxBool = func(l1, l2 int, init bool) [][]bool {
	m := make([][]bool, l1)
	for i := range m {
		m[i] = vctBool(l2, init)
	}
	return m
}

var cbBool = func(l1, l2, l3 int, init bool) [][][]bool {
	c := make([][][]bool, l1)
	for i := range c {
		c[i] = mtxBool(l2, l3, init)
	}
	return c
}

var sz = func(a interface{}) (int, int) {
	switch aa := a.(type) {
	case [][]int:
		return len(aa), len(aa[0])
	case [][]int64:
		return len(aa), len(aa[0])
	case [][]uint:
		return len(aa), len(aa[0])
	case [][]uint64:
		return len(aa), len(aa[0])
	case [][]byte:
		return len(aa), len(aa[0])
	case [][]rune:
		return len(aa), len(aa[0])
	case [][]float64:
		return len(aa), len(aa[0])
	case [][]bool:
		return len(aa), len(aa[0])
	case [][]string:
		return len(aa), len(aa[0])
	case []string:
		return len(aa), len(aa[0])
	default:
		panic("sz")
	}
}

var pop = func(a *[]int) (rst int) {
	rst, *a = elm(*a, -1), (*a)[:len(*a)-1]
	return
}

var elm = func(a []int, i int) int {
	return a[(i+len(a))%len(a)]
}

var rvs = func(a interface{}) {
	switch aa := a.(type) {
	case vector:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case text:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []int:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []int64:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []uint:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []uint64:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []byte:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []rune:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []float64:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []bool:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []string:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []pair:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []triplet:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []vector:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []text:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	case []interface{}:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	default:
		panic("rvs")
	}
}

// string, vector, text
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector, []text,
// []interface{}
var cpRvs = func(a interface{}) interface{} {
	if aa, ok := a.(string); ok {
		t := text(aa)
		rvs(t)
		return string(t)
	}
	rst := cp(a)
	rvs(rst)
	return rst
}

// int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet, vector, text
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector, []text,
// []interface{}
func cp(a interface{}) (rst interface{}) {
	switch aa := a.(type) {
	case int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet:
		rst = a
	case vector:
		rst = make(vector, len(aa))
		copy(rst.(vector), aa)
	case text:
		rst = make(text, len(aa))
		copy(rst.(text), aa)
	case []int:
		rst = make([]int, len(aa))
		copy(rst.([]int), aa)
	case []int64:
		rst = make([]int64, len(aa))
		copy(rst.([]int64), aa)
	case []uint:
		rst = make([]uint, len(aa))
		copy(rst.([]uint), aa)
	case []uint64:
		rst = make([]uint64, len(aa))
		copy(rst.([]uint64), aa)
	case []byte:
		rst = make([]byte, len(aa))
		copy(rst.([]byte), aa)
	case []rune:
		rst = make([]rune, len(aa))
		copy(rst.([]rune), aa)
	case []float64:
		rst = make([]float64, len(aa))
		copy(rst.([]float64), aa)
	case []bool:
		rst = make([]bool, len(aa))
		copy(rst.([]bool), aa)
	case []string:
		rst = make([]string, len(aa))
		copy(rst.([]string), aa)
	case []pair:
		rst = make([]pair, len(aa))
		copy(rst.([]pair), aa)
	case []triplet:
		rst = make([]triplet, len(aa))
		copy(rst.([]triplet), aa)
	case []vector:
		rst = make([]vector, len(aa))
		for i, item := range aa {
			rst.([]vector)[i] = cp(item).(vector)
		}
	case []text:
		rst = make([]text, len(aa))
		for i, item := range aa {
			rst.([]text)[i] = cp(item).(text)
		}
	case []interface{}:
		rst = make([]interface{}, len(aa))
		for i, item := range aa {
			rst.([]interface{})[i] = cp(item)
		}
	default:
		panic("cp")
	}
	return
}

// int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet, vector, text
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector, []text,
// []interface{}
func cmp(a, b interface{}) int {
	switch aa := a.(type) {
	case int:
		return utils.IntComparator(a, b)
	case int64:
		return utils.Int64Comparator(a, b)
	case uint:
		return utils.UIntComparator(a, b)
	case uint64:
		return utils.UInt64Comparator(a, b)
	case byte:
		return utils.ByteComparator(a, b)
	case rune:
		return utils.RuneComparator(a, b)
	case float64:
		return utils.Float64Comparator(a, b)
	case bool:
		return b2i(aa) - b2i(b.(bool))
	case string:
		return utils.StringComparator(a, b)
	case pair:
		bb := b.(pair)
		for i := 0; i < 2; i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return 0
	case triplet:
		bb := b.(triplet)
		for i := 0; i < 3; i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return 0
	case vector:
		bb := b.(vector)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case text:
		bb := b.(text)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []int:
		bb := b.([]int)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []int64:
		bb := b.([]int64)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []uint:
		bb := b.([]uint)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []uint64:
		bb := b.([]uint64)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []byte:
		bb := b.([]byte)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []rune:
		bb := b.([]rune)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []float64:
		bb := b.([]float64)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []bool:
		bb := b.([]bool)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []string:
		bb := b.([]string)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []pair:
		bb := b.([]pair)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []triplet:
		bb := b.([]triplet)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []vector:
		bb := b.([]vector)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []text:
		bb := b.([]text)
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	case []interface{}:
		bb := b.([]interface{})
		for i := 0; i < min(len(aa), len(bb)); i++ {
			if rst := cmp(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return len(aa) - len(bb)
	default:
		panic("cmp")
	}
}

// int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet, vector, text
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector, []text,
// []interface{}
var cmp2 = func(a, b interface{}) int {
	return -cmp(a, b)
}

// int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet, vector, text
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector, []text,
// []interface{}
var eq = func(a, b interface{}) bool {
	return cmp(a, b) == 0
}

// vector, text
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector, []text,
// []interface{}
var srt = func(a interface{}, comparator utils.Comparator, stable bool) {
	if stable {
		sort.SliceStable(a, _less(a, comparator))
	} else {
		sort.Slice(a, _less(a, comparator))
	}
}

// string, vector, text
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector, []text,
// []interface{}
var cpSrt = func(a interface{}, comparator utils.Comparator, stable bool) interface{} {
	if aa, ok := a.(string); ok {
		t := text(aa)
		srt(t, comparator, stable)
		return string(t)
	}
	rst := cp(a)
	srt(rst, comparator, stable)
	return rst
}

func _less(a interface{}, comparator utils.Comparator) func(int, int) bool {
	switch aa := a.(type) {
	case vector:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case text:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []int:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []int64:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []uint:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []uint64:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []byte:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []rune:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []float64:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []bool:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []string:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []pair:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []triplet:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []vector:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []text:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	case []interface{}:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	default:
		panic("_less")
	}
}

// string, vector, text
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector, []text,
// []interface{}
func unq(a interface{}) (rst interface{}) {
	switch aa := a.(type) {
	case string:
		rst = string(unq(text(aa)).(text))
	case vector:
		rst = make(vector, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.(vector), item)
			}
		}
	case text:
		rst = make(text, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.(text), item)
			}
		}
	case []int:
		rst = make([]int, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]int), item)
			}
		}
	case []int64:
		rst = make([]int64, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]int64), item)
			}
		}
	case []uint:
		rst = make([]uint, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]uint), item)
			}
		}
	case []uint64:
		rst = make([]uint64, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]uint64), item)
			}
		}
	case []byte:
		rst = make([]byte, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]byte), item)
			}
		}
	case []rune:
		rst = make([]rune, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]rune), item)
			}
		}
	case []float64:
		rst = make([]float64, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]float64), item)
			}
		}
	case []bool:
		rst = make([]bool, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]bool), item)
			}
		}
	case []string:
		rst = make([]string, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]string), item)
			}
		}
	case []pair:
		rst = make([]pair, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]pair), item)
			}
		}
	case []triplet:
		rst = make([]triplet, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]triplet), item)
			}
		}
	case []vector:
		rst = make([]vector, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]vector), item)
			}
		}
	case []text:
		rst = make([]text, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]text), item)
			}
		}
	case []interface{}:
		rst = make([]interface{}, 0, len(aa))
		for i, item := range aa {
			if i == 0 || !eq(item, aa[i-1]) {
				rst = append(rst.([]interface{}), item)
			}
		}
	default:
		panic("unq")
	}
	return
}

const (
	et byte = 1 << iota
	lt
	gt
	lgt = lt | gt
)

var tp = func(a interface{}) (rst byte) {
	switch aa := a.(type) {
	case string:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case vector:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case text:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []int:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []int64:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []uint:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []uint64:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []byte:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []rune:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []float64:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []bool:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []string:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []pair:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []triplet:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []vector:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []text:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	case []interface{}:
		for i := 1; i < len(aa); i++ {
			rst |= _tp(aa[i-1], aa[i])
		}
	default:
		panic("tp")
	}
	return
}

func _tp(a, b interface{}) byte {
	if rst := cmp(a, b); rst == 0 {
		return et
	} else if rst < 0 {
		return lt
	}
	return gt
}

var bs = func(a, b interface{}, t byte) int {
	switch aa := a.(type) {
	case string:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case vector:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case text:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []int:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []int64:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []uint:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []uint64:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []byte:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []rune:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []float64:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []bool:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []string:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []pair:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []triplet:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []vector:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []text:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	case []interface{}:
		check := func(i int) bool { return _tp(aa[i], b)&t&lgt == 0 }
		if i := lb(-1, len(aa), check); i >= 0 && i < len(aa) && eq(aa[i], b) {
			return i
		}
	default:
		panic("bs")
	}
	return -1
}

var fd = func(l, r, i int, check func(int) bool) int {
	inc := 1
	if i < 0 {
		l, r, i, inc = r, l, -i, -1
	}
	for j := l; (r-j)*inc >= 0; j += inc {
		if i -= b2i(check(j)); i == 0 {
			return j
		}
	}
	return -1
}

var lb = func(l, r int, check func(int) bool) int {
	for l+1 < r {
		if m := l + (r-l)>>1; check(m) {
			r = m
		} else {
			l = m
		}
	}
	return r
}

var ub = func(l, r int, check func(int) bool) int {
	for l+1 < r {
		if m := l + (r-l)>>1; check(m) {
			l = m
		} else {
			r = m
		}
	}
	return l
}

var cnt = func(l, r int, check func(int) bool) (rst int) {
	for i := l; i <= r; i++ {
		rst += b2i(check(i))
	}
	return
}

var (
	drt  = []pair{{-1, 0}, {1, 0}, {0, -1}, {0, 1}}
	drt2 = []pair{{-1, 0}, {1, 0}, {0, -1}, {0, 1}, {-1, -1}, {-1, 1}, {1, -1}, {1, 1}}
)

var srd = func(m, n, i, j int, drt []pair) []pair {
	rst := make([]pair, 0, len(drt))
	for _, d := range drt {
		if x, y := i+d[0], j+d[1]; in(x, y, 0, 0, m-1, n-1) {
			rst = append(rst, pair{x, y})
		}
	}
	return rst
}

var in = func(i, j, x1, y1, x2, y2 int) bool {
	return i >= x1 && i <= x2 && j >= y1 && j <= y2
}

var ug = func(n int, edges [][]int) ([][]pair, []int) {
	g, d := make([][]pair, n), vct(n, 0)
	for _, e := range edges {
		cost := 1
		if len(e) == 3 {
			cost = e[2]
		}
		g[e[0]] = append(g[e[0]], pair{cost, e[1]})
		g[e[1]] = append(g[e[1]], pair{cost, e[0]})
		d[e[0]]++
		d[e[1]]++
	}
	return g, d
}

var dg = func(n int, edges [][]int) ([][]pair, [][]pair, []int, []int) {
	g, rg, id, od := make([][]pair, n), make([][]pair, n), vct(n, 0), vct(n, 0)
	for _, e := range edges {
		cost := 1
		if len(e) == 3 {
			cost = e[2]
		}
		g[e[0]] = append(g[e[0]], pair{cost, e[1]})
		rg[e[1]] = append(rg[e[1]], pair{cost, e[0]})
		od[e[0]]++
		id[e[1]]++
	}
	return g, rg, id, od
}

var child = func(n int, parent []int) [][]int {
	rst := make([][]int, n)
	for c, p := range parent {
		if p >= 0 {
			rst[p] = append(rst[p], c)
		}
	}
	return rst
}

var dijkstra = func(n int, g [][]pair, src int) []int {
	dist, visited, h := vct(n, -1), vctBool(n, false), hp(cmp)
	dist[src] = 0
	h.Push(pair{0, src})
	for !h.Empty() {
		p := h.Pop().(pair)
		if visited[p[1]] {
			continue
		}
		visited[p[1]] = true
		for _, e := range g[p[1]] {
			if d := dist[p[1]] + e[0]; dist[e[1]] < 0 || dist[e[1]] > d {
				dist[e[1]] = d
				h.Push(pair{d, e[1]})
			}
		}
	}
	return dist
}

var tpSort = func(n int, g [][]pair, id []int) []int {
	rst := make([]int, 0, n)
	for p, d := range id {
		if d == 0 {
			rst = append(rst, p)
		}
	}
	for i := 0; i < len(rst); i++ {
		for _, e := range g[rst[i]] {
			if id[e[1]]--; id[e[1]] == 0 {
				rst = append(rst, e[1])
			}
		}
	}
	return rst
}

type (
	pair    [2]int
	triplet [3]int
)

type vector []int

func (v vector) sum() (rst int) {
	for _, n := range v {
		rst += n
	}
	return
}

func (v vector) preSum() []int {
	rst := vct(len(v)+1, 0)
	for i, n := range v {
		rst[i+1] = rst[i] + n
	}
	return rst
}

func (v vector) postSum() []int {
	rst := vct(len(v)+1, 0)
	for i := len(v) - 1; i >= 0; i-- {
		rst[i] = rst[i+1] + v[i]
	}
	return rst
}

func (v vector) left(check func(int, int) bool) []int {
	rst := vct(len(v), 0)
	for i := 0; i < len(v); i++ {
		for rst[i] = i - 1; rst[i] >= 0 && !check(v[rst[i]], v[i]); rst[i] = rst[rst[i]] {
		}
	}
	return rst
}

func (v vector) right(check func(int, int) bool) []int {
	rst := vct(len(v), 0)
	for i := len(v) - 1; i >= 0; i-- {
		for rst[i] = i + 1; rst[i] < len(v) && !check(v[rst[i]], v[i]); rst[i] = rst[rst[i]] {
		}
	}
	return rst
}

func (v vector) counts() map[int]int {
	rst := make(map[int]int, len(v))
	for _, n := range v {
		rst[n]++
	}
	return rst
}

type text []byte

func (t text) split(charSet string) (rst []string) {
	var m [256]bool
	for _, c := range text(charSet) {
		m[c] = true
	}
	i := -1
	for j, c := range append(t, charSet[0]) {
		if !m[c] {
			continue
		}
		if j > i+1 {
			rst = append(rst, string(t[i+1:j]))
		}
		i = j
	}
	return
}

func (t text) counts() (rst [256]int) {
	for _, c := range t {
		rst[c]++
	}
	return
}

type heap struct {
	*binaryheap.Heap
}

var hp = func(comparator utils.Comparator) *heap {
	return &heap{binaryheap.NewWith(comparator)}
}

func (h *heap) Pop() interface{} {
	rst, _ := h.Heap.Pop()
	return rst
}

func (h *heap) Peek() interface{} {
	rst, _ := h.Heap.Peek()
	return rst
}

type treeMap struct {
	*redblacktree.Tree
}

var tm = func(comparator utils.Comparator) *treeMap {
	return &treeMap{redblacktree.NewWith(comparator)}
}

func (m *treeMap) Floor(x interface{}) *redblacktree.Node {
	rst, _ := m.Tree.Floor(x)
	return rst
}

func (m *treeMap) Ceiling(x interface{}) *redblacktree.Node {
	rst, _ := m.Tree.Ceiling(x)
	return rst
}

type treeSet struct {
	*treeMap
}

var ts = func(comparator utils.Comparator) *treeSet {
	return &treeSet{tm(comparator)}
}

func (s *treeSet) Put(items ...interface{}) {
	for _, item := range items {
		s.Tree.Put(item, struct{}{})
	}
}

func (s *treeSet) Remove(items ...interface{}) {
	for _, item := range items {
		s.Tree.Remove(item)
	}
}

func (s *treeSet) contains(items ...interface{}) bool {
	for _, item := range items {
		if _, found := s.Get(item); !found {
			return false
		}
	}
	return true
}

func (s *treeSet) containsAny(items ...interface{}) bool {
	for _, item := range items {
		if _, found := s.Get(item); found {
			return true
		}
	}
	return false
}

func (s *treeSet) Values() []interface{} {
	return s.Keys()
}

func (s *treeSet) intersection(another *treeSet) *treeSet {
	rst := ts(s.Comparator)
	for it := s.Iterator(); it.Next(); {
		if item := it.Key(); another.contains(item) {
			rst.Put(item)
		}
	}
	return rst
}

func (s *treeSet) union(another *treeSet) *treeSet {
	rst := ts(s.Comparator)
	for it := s.Iterator(); it.Next(); {
		rst.Put(it.Key())
	}
	for it := another.Iterator(); it.Next(); {
		rst.Put(it.Key())
	}
	return rst
}

func (s *treeSet) difference(another *treeSet) *treeSet {
	rst := ts(s.Comparator)
	for it := s.Iterator(); it.Next(); {
		if item := it.Key(); !another.contains(item) {
			rst.Put(item)
		}
	}
	return rst
}

func (s *treeSet) min() interface{} {
	return s.Left().Key
}

func (s *treeSet) max() interface{} {
	return s.Right().Key
}

func (s *treeSet) floor(x interface{}) interface{} {
	if node := s.Floor(x); node != nil {
		return node.Key
	}
	return nil
}

func (s *treeSet) ceiling(x interface{}) interface{} {
	if node := s.Ceiling(x); node != nil {
		return node.Key
	}
	return nil
}

type multiSet struct {
	*treeSet
	cnt *treeMap
}

type _item struct {
	val interface{}
	idx int
}

var mts = func(comparator utils.Comparator) *multiSet {
	return &multiSet{
		treeSet: ts(func(a, b interface{}) int {
			aa, bb := a.(_item), b.(_item)
			if rst := comparator(aa.val, bb.val); rst != 0 {
				return rst
			}
			return aa.idx - bb.idx
		}),
		cnt: tm(comparator),
	}
}

func (s *multiSet) Put(items ...interface{}) {
	for _, item := range items {
		//if node := s.cnt.GetNode(item); node != nil {
		//	cnt := node.Value.(int)
		//	s.treeSet.Put(_item{item, cnt})
		//	node.Value = cnt + 1
		//} else {
		//	s.treeSet.Put(_item{item, 0})
		//	s.cnt.Put(item, 1)
		//}
		cnt := 0
		if val, found := s.cnt.Get(item); found {
			cnt = val.(int)
		}
		s.treeSet.Put(_item{item, cnt})
		s.cnt.Put(item, cnt+1)
	}
}

func (s *multiSet) Remove(items ...interface{}) {
	for _, item := range items {
		//if node := s.cnt.GetNode(item); node != nil {
		//	cnt := node.Value.(int)
		//	if cnt--; cnt == 0 {
		//		s.cnt.Remove(item)
		//	} else {
		//		node.Value = cnt
		//	}
		//	s.treeSet.Remove(_item{item, cnt})
		//}
		if val, found := s.cnt.Get(item); found {
			cnt := val.(int)
			if cnt--; cnt == 0 {
				s.cnt.Remove(item)
			} else {
				s.cnt.Put(item, cnt)
			}
			s.treeSet.Remove(_item{item, cnt})
		}
	}
}

func (s *multiSet) removeAll(items ...interface{}) {
	for _, item := range items {
		if val, found := s.cnt.Get(item); found {
			s.cnt.Remove(item)
			cnt := val.(int)
			for cnt--; cnt >= 0; cnt-- {
				s.treeSet.Remove(_item{item, cnt})
			}
		}
	}
}

func (s *multiSet) contains(items ...interface{}) bool {
	for _, item := range items {
		if _, found := s.cnt.Get(item); !found {
			return false
		}
	}
	return true
}

func (s *multiSet) containsAny(items ...interface{}) bool {
	for _, item := range items {
		if _, found := s.cnt.Get(item); found {
			return true
		}
	}
	return false
}

func (s *multiSet) Clear() {
	s.treeSet.Clear()
	s.cnt.Clear()
}

func (s *multiSet) Values() []interface{} {
	rst := make([]interface{}, s.Size())
	for i, item := range s.treeSet.Values() {
		rst[i] = item.(_item).val
	}
	return rst
}

func (s *multiSet) min() interface{} {
	return s.treeSet.min().(_item).val
}

func (s *multiSet) max() interface{} {
	return s.treeSet.max().(_item).val
}

func (s *multiSet) floor(x interface{}) interface{} {
	if item := s.treeSet.floor(_item{x, 0}); item != nil {
		return item.(_item).val
	}
	return nil
}

func (s *multiSet) ceiling(x interface{}) interface{} {
	if item := s.treeSet.ceiling(_item{x, 0}); item != nil {
		return item.(_item).val
	}
	return nil
}

var hs = func(a interface{}) *hashset.Set {
	s := hashset.New()
	if a == nil {
		return s
	}
	switch aa := a.(type) {
	case string:
		for _, item := range text(aa) {
			s.Add(item)
		}
	case vector:
		for _, item := range aa {
			s.Add(item)
		}
	case text:
		for _, item := range aa {
			s.Add(item)
		}
	case []int:
		for _, item := range aa {
			s.Add(item)
		}
	case []int64:
		for _, item := range aa {
			s.Add(item)
		}
	case []uint:
		for _, item := range aa {
			s.Add(item)
		}
	case []uint64:
		for _, item := range aa {
			s.Add(item)
		}
	case []byte:
		for _, item := range aa {
			s.Add(item)
		}
	case []rune:
		for _, item := range aa {
			s.Add(item)
		}
	case []float64:
		for _, item := range aa {
			s.Add(item)
		}
	case []bool:
		for _, item := range aa {
			s.Add(item)
		}
	case []string:
		for _, item := range aa {
			s.Add(item)
		}
	case []pair:
		for _, item := range aa {
			s.Add(item)
		}
	case []triplet:
		for _, item := range aa {
			s.Add(item)
		}
	case []interface{}:
		s.Add(aa...)
	default:
		panic("hs")
	}
	return s
}

type deque struct {
	*list.List
}

var dq = func() *deque {
	return &deque{list.New()}
}

func (q *deque) empty() bool {
	return q.Len() == 0
}

func (q *deque) popFront() interface{} {
	return q.Remove(q.Front())
}

func (q *deque) popBack() interface{} {
	return q.Remove(q.Back())
}

var (
	_          = big.NewInt
	_          = bits.Len
	_          = bits.Reverse
	_          = bits.OnesCount
	_, _       = bits.LeadingZeros, bits.TrailingZeros
	_          = strings.Map
	_          = strings.Join
	_          = strings.Count
	_          = strings.Repeat
	_          = strings.Replace
	_          = strings.EqualFold
	_, _       = strings.ToLower, strings.ToUpper
	_, _       = strings.SplitN, strings.SplitAfterN
	_, _       = strings.HasPrefix, strings.HasSuffix
	_, _       = strings.Contains, strings.ContainsAny
	_, _, _    = strings.Index, strings.IndexAny, strings.IndexFunc
	_, _, _    = strings.LastIndex, strings.LastIndexAny, strings.LastIndexFunc
	_, _, _, _ = strings.Trim, strings.TrimFunc, strings.TrimPrefix, strings.TrimSuffix
	_, _, _, _ = strings.TrimLeft, strings.TrimLeftFunc, strings.TrimRight, strings.TrimRightFunc

	_, _                               = prt, prf
	_, _, _                            = s2i, i2s, b2i
	_, _, _, _, _, _                   = isNumber, isLetter, isLower, isUpper, toLower, toUpper
	_, _, _, _, _, _, _, _, _          = abs, min, max, pow, gcd, lcm, c, isPrime, factor
	_, _, _, _, _, _                   = vct, mtx, cb, vctBool, mtxBool, cbBool
	_, _, _, _, _, _, _, _, _, _, _, _ = sz, pop, elm, rvs, cpRvs, cp, cmp, cmp2, eq, srt, cpSrt, unq
	_, _, _, _, _, _, _, _, _, _       = et, lt, gt, lgt, tp, bs, fd, lb, ub, cnt
	_, _, _, _, _, _, _, _, _          = drt, drt2, srd, in, ug, dg, child, dijkstra, tpSort
	_, _, _, _                         = pair{}, triplet{}, vector{}, text{}
	_, _, _, _, _, _                   = heap{}, treeMap{}, treeSet{}, multiSet{}, hashset.Set{}, deque{}
	_, _, _, _, _, _                   = hp, tm, ts, mts, hs, dq
)

const mod int = 1e9 + 7

//type ListNode struct {
//	Val  int
//	Next *ListNode
//}

//type TreeNode struct {
//	Val         int
//	Left, Right *TreeNode
//}

//func init() {
//	_initC(1000, 0)
//}
