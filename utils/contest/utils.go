package contest

import (
	"container/list"
	"fmt"
	"math"
	"reflect"
	"sort"
	"strconv"

	"github.com/emirpasic/gods/sets/hashset"
	"github.com/emirpasic/gods/trees/binaryheap"
	"github.com/emirpasic/gods/trees/redblacktree"
	"github.com/emirpasic/gods/utils"
)

func _assert(info interface{}, conditions ...bool) {
	for _, condition := range conditions {
		if !condition {
			panic(info)
		}
	}
}

func _ternary(condition bool, a, b int) int {
	if condition {
		return a
	}
	return b
}

var prt, prf = fmt.Println, fmt.Printf

var s2i = func(s string, base int) int {
	rst, err := strconv.ParseInt(s, base, 64)
	if err != nil {
		prt(err)
	}
	return int(rst)
}

var i2s = func(i, base int) string {
	return strconv.FormatInt(int64(i), base)
}

var b2i = func(b bool) int {
	return _ternary(b, 1, 0)
}

var isNumber = func(a interface{}) bool {
	switch aa := a.(type) {
	case byte:
		return aa >= '0' && aa <= '9'
	case rune:
		return aa >= '0' && aa <= '9'
	default:
		panic("isNumber")
	}
}

var isLetter = func(a interface{}) bool {
	return isLower(a) || isUpper(a)
}

var isLower = func(a interface{}) bool {
	switch aa := a.(type) {
	case byte:
		return aa >= 'a' && aa <= 'z'
	case rune:
		return aa >= 'a' && aa <= 'z'
	default:
		panic("isLower")
	}
}

var isUpper = func(a interface{}) bool {
	switch aa := a.(type) {
	case byte:
		return aa >= 'A' && aa <= 'Z'
	case rune:
		return aa >= 'A' && aa <= 'Z'
	default:
		panic("isUpper")
	}
}

const mod int = 1e9 + 7

var abs = func(a int) int {
	return _ternary(a >= 0, a, -a)
}

var min = func(nums ...int) int {
	_assert("min", len(nums) > 0)
	rst := math.MaxInt
	for _, n := range nums {
		rst = _ternary(n < rst, n, rst)
	}
	return rst
}

var max = func(nums ...int) int {
	_assert("max", len(nums) > 0)
	rst := math.MinInt
	for _, n := range nums {
		rst = _ternary(n > rst, n, rst)
	}
	return rst
}

var pow = func(a, b, mod int) (rst int) {
	_assert("pow", b >= 0, a != 0 || b != 0)
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
	_assert("gcd", a > 0, b > 0)
	if a%b == 0 {
		return b
	}
	return gcd(b, a%b)
}

var lcm = func(a, b int) int {
	return a / gcd(a, b) * b
}

var c [][]int

//func init() {
//	n, mod := 1000, 0
//	c = mtx(n+1, n+1, 0)
//	for i := 0; i <= n; i++ {
//		c[i][0] = 1
//		for j := 1; j <= i; j++ {
//			if c[i][j] = c[i-1][j-1] + c[i-1][j]; mod > 1 {
//				c[i][j] %= mod
//			}
//		}
//	}
//}

var isPrime = func(n int) bool {
	_assert("isPrime", n >= 0)
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
	_assert("factor", n >= 0)
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

var pop = func(a interface{}) (rst interface{}) {
	switch aa := a.(type) {
	case *[]int:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]int64:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]uint:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]uint64:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]byte:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]rune:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]float64:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]bool:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]string:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]pair:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]triplet:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]vector:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	case *[]interface{}:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	default:
		panic("pop")
	}
	return
}

var back = func(a interface{}) interface{} {
	switch aa := a.(type) {
	case []int:
		return aa[len(aa)-1]
	case []int64:
		return aa[len(aa)-1]
	case []uint:
		return aa[len(aa)-1]
	case []uint64:
		return aa[len(aa)-1]
	case []byte:
		return aa[len(aa)-1]
	case []rune:
		return aa[len(aa)-1]
	case []float64:
		return aa[len(aa)-1]
	case []bool:
		return aa[len(aa)-1]
	case []string:
		return aa[len(aa)-1]
	case []pair:
		return aa[len(aa)-1]
	case []triplet:
		return aa[len(aa)-1]
	case []vector:
		return aa[len(aa)-1]
	case []interface{}:
		return aa[len(aa)-1]
	default:
		panic("back")
	}
}

var rvs = func(a interface{}) {
	switch aa := a.(type) {
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
	case []interface{}:
		for i, j := 0, len(aa)-1; i < j; i, j = i+1, j-1 {
			aa[i], aa[j] = aa[j], aa[i]
		}
	default:
		panic("rvs")
	}
}

// int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet, vector
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector,
// []interface{}
func cp(a interface{}) (rst interface{}) {
	switch aa := a.(type) {
	case int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet:
		rst = a
	case vector:
		rst = vector(make([]int, len(aa)))
		copy(rst.(vector), aa)
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

// int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet, vector
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector,
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

// int, int64, uint, uint64, byte, rune, float64, bool, string, pair, triplet, vector
//
// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector,
// []interface{}
var cmp2 = func(a, b interface{}) int {
	return -cmp(a, b)
}

// []int, []int64, []uint, []uint64, []byte, []rune, []float64, []bool, []string, []pair, []triplet, []vector,
// []interface{}
var srt = func(a interface{}, comparator utils.Comparator) {
	sort.Slice(a, _less(a, comparator))
}

func _less(a interface{}, comparator utils.Comparator) func(int, int) bool {
	switch aa := a.(type) {
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
	case []interface{}:
		return func(i, j int) bool { return comparator(aa[i], aa[j]) < 0 }
	default:
		panic("_less")
	}
}

var fd = func(l, r, i int, check func(int) bool) int {
	_assert("fd", l <= r, i != 0)
	inc := 1
	if i < 0 {
		l, r, i, inc = r, l, -i, -1
	}
	for j := l; j != r+inc; j += inc {
		if i -= b2i(check(j)); i == 0 {
			return j
		}
	}
	return -1
}

var lb = func(l, r int, check func(int) bool) int {
	_assert("lb", l < r)
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
	_assert("ub", l < r)
	for l+1 < r {
		if m := l + (r-l)>>1; check(m) {
			l = m
		} else {
			r = m
		}
	}
	return l
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
	_assert("text_split", len(charSet) > 0)
	m := make(map[byte]struct{}, len(charSet))
	for _, c := range text(charSet) {
		m[c] = struct{}{}
	}
	i := -1
	for j, c := range append(t, charSet[0]) {
		if _, ok := m[c]; !ok {
			continue
		}
		if j > i+1 {
			rst = append(rst, string(t[i+1:j]))
		}
		i = j
	}
	return
}

func (t text) counts() map[byte]int {
	rst := make(map[byte]int, 256)
	for _, c := range t {
		rst[c]++
	}
	return rst
}

var (
	drt  = []pair{{-1, 0}, {1, 0}, {0, -1}, {0, 1}}
	drt2 = []pair{{-1, 0}, {1, 0}, {0, -1}, {0, 1}, {-1, -1}, {-1, 1}, {1, -1}, {1, 1}}
)

var srd = func(m, n, i, j int, drt []pair) []pair {
	_assert("srd", in(i, j, 0, 0, m-1, n-1))
	rst := make([]pair, 0, len(drt))
	for _, d := range drt {
		if x, y := i+d[0], j+d[1]; in(x, y, 0, 0, m-1, n-1) {
			rst = append(rst, pair{x, y})
		}
	}
	return rst
}

var in = func(i, j, x1, y1, x2, y2 int) bool {
	_assert("in", x1 <= x2, y1 <= y2)
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
	for i, d := range id {
		if d == 0 {
			rst = append(rst, i)
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

type heap struct {
	*binaryheap.Heap
}

var hp = func(comparator utils.Comparator) *heap {
	return &heap{binaryheap.NewWith(comparator)}
}

func (h *heap) Pop() interface{} {
	_assert("heap_Pop", !h.Empty())
	rst, _ := h.Heap.Pop()
	return rst
}

func (h *heap) Peek() interface{} {
	_assert("heap_Peek", !h.Empty())
	rst, _ := h.Heap.Peek()
	return rst
}

type treeMap struct {
	*redblacktree.Tree
}

var tm = func(comparator utils.Comparator) *treeMap {
	return &treeMap{redblacktree.NewWith(comparator)}
}

func (m *treeMap) Left() *redblacktree.Node {
	_assert("treeMap_Left", !m.Empty())
	return m.Tree.Left()
}

func (m *treeMap) Right() *redblacktree.Node {
	_assert("treeMap_Right", !m.Empty())
	return m.Tree.Right()
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

func (s *treeSet) Values() []interface{} {
	return s.Keys()
}

func (s *treeSet) intersection(another *treeSet) *treeSet {
	_assert(reflect.ValueOf(s.Comparator).Pointer() == reflect.ValueOf(another.Comparator).Pointer())
	rst := ts(s.Comparator)
	for it := s.Iterator(); it.Next(); {
		if item := it.Key(); another.contains(item) {
			rst.Put(item)
		}
	}
	return rst
}

func (s *treeSet) union(another *treeSet) *treeSet {
	_assert(reflect.ValueOf(s.Comparator).Pointer() == reflect.ValueOf(another.Comparator).Pointer())
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
	_assert(reflect.ValueOf(s.Comparator).Pointer() == reflect.ValueOf(another.Comparator).Pointer())
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
			key := comparator(aa.val, bb.val)
			return _ternary(key != 0, key, aa.idx-bb.idx)
		}),
		cnt: tm(comparator),
	}
}

func (s *multiSet) Put(items ...interface{}) {
	for _, item := range items {
		if node := s.cnt.GetNode(item); node != nil {
			cnt := node.Value.(int)
			s.treeSet.Put(_item{item, cnt})
			node.Value = cnt + 1
		} else {
			s.treeSet.Put(_item{item, 0})
			s.cnt.Put(item, 1)
		}
	}
}

func (s *multiSet) Remove(items ...interface{}) {
	for _, item := range items {
		if node := s.cnt.GetNode(item); node != nil {
			cnt := node.Value.(int)
			if cnt--; cnt == 0 {
				s.cnt.Remove(item)
			} else {
				node.Value = cnt
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

func (s *multiSet) Clear() {
	s.treeSet.Clear()
	s.cnt.Clear()
}

func (s *multiSet) Values() []interface{} {
	items := s.treeSet.Values()
	rst := make([]interface{}, 0, len(items))
	for _, item := range items {
		rst = append(rst, item.(_item).val)
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
	switch aa := a.(type) {
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
	_assert("deque_popFront", !q.empty())
	return q.Remove(q.Front())
}

func (q *deque) popBack() interface{} {
	_assert("deque_popBack", !q.empty())
	return q.Remove(q.Back())
}
