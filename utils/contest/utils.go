package contest

import (
	"container/list"
	"fmt"
	"math"
	"sort"
	"strconv"

	"github.com/emirpasic/gods/maps/treemap"
	"github.com/emirpasic/gods/trees/binaryheap"
	"github.com/emirpasic/gods/utils"
)

func _assert(conditions ...bool) {
	for _, condition := range conditions {
		if !condition {
			panic(nil)
		}
	}
}

func _ternary(condition bool, a, b int) int {
	if condition {
		return a
	}
	return b
}

var (
	prt = fmt.Println
	prf = fmt.Printf
)

func btw(a, l, r int) bool {
	_assert(l <= r)
	return a >= l && a <= r
}

func in(a int, nums ...int) bool {
	for _, n := range nums {
		if n == a {
			return true
		}
	}
	return false
}

func s2i(s string, base int) int {
	rst, _ := strconv.ParseInt(s, base, 64)
	return int(rst)
}

func i2s(i, base int) string {
	return strconv.FormatInt(int64(i), base)
}

func b2i(b bool) int {
	return _ternary(b, 1, 0)
}

func isNumber(a interface{}) bool {
	switch aa := a.(type) {
	case byte:
		return aa >= '0' && aa <= '9'
	case rune:
		return aa >= '0' && aa <= '9'
	default:
		panic(nil)
	}
}

func isLetter(a interface{}) bool {
	return isLower(a) || isUpper(a)
}

func isLower(a interface{}) bool {
	switch aa := a.(type) {
	case byte:
		return aa >= 'a' && aa <= 'z'
	case rune:
		return aa >= 'a' && aa <= 'z'
	default:
		panic(nil)
	}
}

func isUpper(a interface{}) bool {
	switch aa := a.(type) {
	case byte:
		return aa >= 'A' && aa <= 'Z'
	case rune:
		return aa >= 'A' && aa <= 'Z'
	default:
		panic(nil)
	}
}

const mod int = 1e9 + 7

func abs(a int) int {
	return _ternary(a >= 0, a, -a)
}

func max(a, b int, nums ...int) int {
	rst := _ternary(a >= b, a, b)
	for _, n := range nums {
		rst = _ternary(n > rst, n, rst)
	}
	return rst
}

func min(a, b int, nums ...int) int {
	rst := _ternary(a <= b, a, b)
	for _, n := range nums {
		rst = _ternary(n < rst, n, rst)
	}
	return rst
}

func pow(a, b, mod int) (rst int) {
	_assert(b >= 0, a != 0 || b != 0)
	switch a {
	case 0, 1:
		return a
	case -1:
		return _ternary(b&1 == 0, 1, -1)
	default:
		for rst = 1; b > 0; b >>= 1 {
			if b&1 != 0 {
				if rst *= a; mod > 0 {
					rst %= mod
				}
			}
			if a *= a; mod > 0 {
				a %= mod
			}
		}
		return
	}
}

func gcd(a, b int) int {
	_assert(a > 0, b > 0)
	if a%b == 0 {
		return b
	}
	return gcd(b, a%b)
}

func lcm(a, b int) int {
	_assert(a > 0, b > 0)
	return a / gcd(a, b) * b
}

var cache [][]int

//func init() {
//	cache = mtx(1001, 1001, 0)
//}

func c(n, k, mod int) (rst int) {
	_assert(n > 0, btw(k, 0, n))
	if cache[n][k] > 0 {
		return cache[n][k]
	}
	defer func() {
		cache[n][k], cache[n][n-k] = rst, rst
	}()
	if k = _ternary(k > n>>1, n-k, k); k == 0 {
		return 1
	}
	if rst = c(n-1, k-1, mod) + c(n-1, k, mod); mod > 0 {
		rst %= mod
	}
	return
}

func isPrime(n int) bool {
	_assert(n >= 0)
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

func factor(n int) map[int]int {
	_assert(n >= 0)
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

func vct(l, init int) []int {
	v := make([]int, l)
	if init != 0 {
		for i := range v {
			v[i] = init
		}
	}
	return v
}

func vctBool(l int, init bool) []bool {
	v := make([]bool, l)
	if init {
		for i := range v {
			v[i] = true
		}
	}
	return v
}

func mtx(l1, l2, init int) [][]int {
	m := make([][]int, l1)
	for i := range m {
		m[i] = vct(l2, init)
	}
	return m
}

func mtxBool(l1, l2 int, init bool) [][]bool {
	m := make([][]bool, l1)
	for i := range m {
		m[i] = vctBool(l2, init)
	}
	return m
}

func cb(l1, l2, l3, init int) [][][]int {
	c := make([][][]int, l1)
	for i := range c {
		c[i] = mtx(l2, l3, init)
	}
	return c
}

func push(a, item interface{}) {
	switch aa := a.(type) {
	case *[]int:
		*aa = append(*aa, item.(int))
	case *[]int64:
		*aa = append(*aa, item.(int64))
	case *[]uint:
		*aa = append(*aa, item.(uint))
	case *[]uint64:
		*aa = append(*aa, item.(uint64))
	case *[]byte:
		*aa = append(*aa, item.(byte))
	case *[]rune:
		*aa = append(*aa, item.(rune))
	case *[]float64:
		*aa = append(*aa, item.(float64))
	case *[]bool:
		*aa = append(*aa, item.(bool))
	case *[]string:
		*aa = append(*aa, item.(string))
	case *[]pair:
		*aa = append(*aa, item.(pair))
	case *[]interface{}:
		*aa = append(*aa, item)
	default:
		panic(nil)
	}
}

func pop(a interface{}) (rst interface{}) {
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
	case *[]interface{}:
		rst, *aa = back(*aa), (*aa)[:len(*aa)-1]
	default:
		panic(nil)
	}
	return
}

func back(a interface{}) interface{} {
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
	case []interface{}:
		return aa[len(aa)-1]
	default:
		panic(nil)
	}
}

func reverse(a interface{}) {
	switch aa := a.(type) {
	case *[]int:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]int64:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]uint:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]uint64:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]byte:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]rune:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]float64:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]bool:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]string:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]pair:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	case *[]interface{}:
		for i, j := 0, len(*aa)-1; i < j; i, j = i+1, j-1 {
			(*aa)[i], (*aa)[j] = (*aa)[j], (*aa)[i]
		}
	default:
		panic(nil)
	}
}

var (
	intComparator2     = func(a, b interface{}) int { return -utils.IntComparator(a, b) }
	int64Comparator2   = func(a, b interface{}) int { return -utils.Int64Comparator(a, b) }
	uintComparator2    = func(a, b interface{}) int { return -utils.UIntComparator(a, b) }
	uint64Comparator2  = func(a, b interface{}) int { return -utils.UInt64Comparator(a, b) }
	byteComparator2    = func(a, b interface{}) int { return -utils.ByteComparator(a, b) }
	runeComparator2    = func(a, b interface{}) int { return -utils.RuneComparator(a, b) }
	float64Comparator2 = func(a, b interface{}) int { return -utils.Float64Comparator(a, b) }
	stringComparator2  = func(a, b interface{}) int { return -utils.StringComparator(a, b) }
	pairComparator2    = func(a, b interface{}) int { return -pairComparator(a, b) }
)

func srt(a interface{}, comparator utils.Comparator) {
	switch aa := a.(type) {
	case *[]int:
		sort.Sort(_sliceInt{aa, comparator})
	case *[]int64:
		sort.Sort(_sliceInt64{aa, comparator})
	case *[]uint:
		sort.Sort(_sliceUint{aa, comparator})
	case *[]uint64:
		sort.Sort(_sliceUint64{aa, comparator})
	case *[]byte:
		sort.Sort(_sliceByte{aa, comparator})
	case *[]rune:
		sort.Sort(_sliceRune{aa, comparator})
	case *[]float64:
		sort.Sort(_sliceFloat{aa, comparator})
	case *[]string:
		sort.Sort(_sliceString{aa, comparator})
	case *[]pair:
		sort.Sort(_slicePair{aa, comparator})
	default:
		panic(nil)
	}
}

type (
	_sliceInt struct {
		values     *[]int
		comparator utils.Comparator
	}
	_sliceInt64 struct {
		values     *[]int64
		comparator utils.Comparator
	}
	_sliceUint struct {
		values     *[]uint
		comparator utils.Comparator
	}
	_sliceUint64 struct {
		values     *[]uint64
		comparator utils.Comparator
	}
	_sliceByte struct {
		values     *[]byte
		comparator utils.Comparator
	}
	_sliceRune struct {
		values     *[]rune
		comparator utils.Comparator
	}
	_sliceFloat struct {
		values     *[]float64
		comparator utils.Comparator
	}
	_sliceString struct {
		values     *[]string
		comparator utils.Comparator
	}
	_slicePair struct {
		values     *[]pair
		comparator utils.Comparator
	}
)

func (s _sliceInt) Len() int              { return len(*s.values) }
func (s _sliceInt) Swap(i, j int)         { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _sliceInt) Less(i, j int) bool    { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }
func (s _sliceInt64) Len() int            { return len(*s.values) }
func (s _sliceInt64) Swap(i, j int)       { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _sliceInt64) Less(i, j int) bool  { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }
func (s _sliceUint) Len() int             { return len(*s.values) }
func (s _sliceUint) Swap(i, j int)        { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _sliceUint) Less(i, j int) bool   { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }
func (s _sliceUint64) Len() int           { return len(*s.values) }
func (s _sliceUint64) Swap(i, j int)      { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _sliceUint64) Less(i, j int) bool { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }
func (s _sliceByte) Len() int             { return len(*s.values) }
func (s _sliceByte) Swap(i, j int)        { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _sliceByte) Less(i, j int) bool   { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }
func (s _sliceRune) Len() int             { return len(*s.values) }
func (s _sliceRune) Swap(i, j int)        { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _sliceRune) Less(i, j int) bool   { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }
func (s _sliceFloat) Len() int            { return len(*s.values) }
func (s _sliceFloat) Swap(i, j int)       { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _sliceFloat) Less(i, j int) bool  { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }
func (s _sliceString) Len() int           { return len(*s.values) }
func (s _sliceString) Swap(i, j int)      { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _sliceString) Less(i, j int) bool { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }
func (s _slicePair) Len() int             { return len(*s.values) }
func (s _slicePair) Swap(i, j int)        { (*s.values)[i], (*s.values)[j] = (*s.values)[j], (*s.values)[i] }
func (s _slicePair) Less(i, j int) bool   { return s.comparator((*s.values)[i], (*s.values)[j]) < 0 }

type vector []int

func (v vector) max() int {
	_assert(len(v) > 0)
	rst := math.MinInt64
	for _, n := range v {
		rst = max(rst, n)
	}
	return rst
}

func (v vector) min() int {
	_assert(len(v) > 0)
	rst := math.MaxInt64
	for _, n := range v {
		rst = min(rst, n)
	}
	return rst
}

func (v vector) sum() (rst int) {
	for _, n := range v {
		rst += n
	}
	return
}

func (v vector) preSum() []int {
	rst := vct(len(v)+1, 0)
	for i := 1; i <= len(v); i++ {
		rst[i] = rst[i-1] + v[i-1]
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

type text string

func (t text) counts() map[rune]int {
	rst := make(map[rune]int, len(t))
	for _, c := range t {
		rst[c]++
	}
	return rst
}

type pair [2]int

var pairComparator = func(a, b interface{}) int {
	aa, bb := a.(pair), b.(pair)
	return _ternary(aa[0] != bb[0], aa[0]-bb[0], aa[1]-bb[1])
}

func ug(n int, edges [][]int) ([][]pair, []int) {
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

func dg(n int, edges [][]int) ([][]pair, [][]pair, []int, []int) {
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

func dijkstra(n int, g [][]pair, src int) []int {
	dist, visited, h := vct(n, -1), vctBool(n, false), hp(pairComparator)
	dist[src] = 0
	h.Push(pair{0, src})
	for !h.Empty() {
		peek := h.pop().(pair)
		if visited[peek[1]] {
			continue
		}
		visited[peek[1]] = true
		for _, e := range g[peek[1]] {
			if d := dist[peek[1]] + e[0]; !btw(dist[e[1]], 0, d) {
				dist[e[1]] = d
				h.Push(pair{d, e[1]})
			}
		}
	}
	return dist
}

func tpSort(n int, g [][]pair, id []int) []int {
	rst := make([]int, 0, n)
	for i, d := range id {
		if d == 0 {
			push(&rst, i)
		}
	}
	for i := 0; i < len(rst); i++ {
		for _, e := range g[rst[i]] {
			if id[e[1]]--; id[e[1]] == 0 {
				push(&rst, e[1])
			}
		}
	}
	return rst
}

type heap struct {
	*binaryheap.Heap
}

func hp(comparator utils.Comparator) *heap {
	return &heap{binaryheap.NewWith(comparator)}
}

func (h *heap) peek() interface{} {
	_assert(!h.Empty())
	rst, _ := h.Peek()
	return rst
}

func (h *heap) pop() interface{} {
	_assert(!h.Empty())
	rst, _ := h.Pop()
	return rst
}

type treeSet struct {
	*treemap.Map
}

func ts(comparator utils.Comparator) *treeSet {
	return &treeSet{treemap.NewWith(comparator)}
}

func (s *treeSet) add(items ...interface{}) {
	for _, item := range items {
		s.Put(item, nil)
	}
}

func (s *treeSet) remove(items ...interface{}) {
	for _, item := range items {
		s.Remove(item)
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

func (s *treeSet) values() []interface{} {
	return s.Keys()
}

func (s *treeSet) min() interface{} {
	_assert(!s.Empty())
	rst, _ := s.Min()
	return rst
}

func (s *treeSet) max() interface{} {
	_assert(!s.Empty())
	rst, _ := s.Max()
	return rst
}

func (s *treeSet) floor(x interface{}) interface{} {
	rst, _ := s.Floor(x)
	return rst
}

func (s *treeSet) ceiling(x interface{}) interface{} {
	rst, _ := s.Ceiling(x)
	return rst
}

type multiSet struct {
	*treemap.Map
	cnt map[interface{}]int
}

type _pair struct {
	val interface{}
	idx int
}

func _wrapComparator(comparator utils.Comparator) utils.Comparator {
	return func(a, b interface{}) int {
		aa, bb := a.(_pair), b.(_pair)
		key := comparator(aa.val, bb.val)
		return _ternary(key != 0, key, aa.idx-bb.idx)
	}
}

func mts(comparator utils.Comparator) *multiSet {
	return &multiSet{
		Map: treemap.NewWith(_wrapComparator(comparator)),
		cnt: make(map[interface{}]int),
	}
}

func (s *multiSet) add(items ...interface{}) {
	for _, item := range items {
		s.Put(_pair{item, s.cnt[item]}, nil)
		s.cnt[item]++
	}
}

func (s *multiSet) remove(items ...interface{}) {
	for _, item := range items {
		if s.cnt[item] > 0 {
			s.cnt[item]--
			s.Remove(_pair{item, s.cnt[item]})
		}
	}
}

func (s *multiSet) contains(items ...interface{}) bool {
	for _, item := range items {
		if s.cnt[item] == 0 {
			return false
		}
	}
	return true
}

func (s *multiSet) values() []interface{} {
	values := s.Keys()
	rst := make([]interface{}, 0, len(values))
	for _, val := range values {
		push(&rst, val.(_pair).val)
	}
	return rst
}

func (s *multiSet) min() interface{} {
	_assert(!s.Empty())
	rst, _ := s.Min()
	return rst.(_pair).val
}

func (s *multiSet) max() interface{} {
	_assert(!s.Empty())
	rst, _ := s.Max()
	return rst.(_pair).val
}

func (s *multiSet) floor(x interface{}) interface{} {
	rst, _ := s.Floor(_pair{x, 0})
	return rst.(_pair).val
}

func (s *multiSet) ceiling(x interface{}) interface{} {
	rst, _ := s.Ceiling(_pair{x, 0})
	return rst.(_pair).val
}

type deque struct {
	*list.List
}

func (q *deque) popFront() interface{} {
	_assert(q.Len() > 0)
	return q.Remove(q.Front())
}

func (q *deque) popBack() interface{} {
	_assert(q.Len() > 0)
	return q.Remove(q.Back())
}

type trieNode struct {
	children       []*trieNode
	parent         *trieNode
	curCnt, subCnt int
}

func newTrieNode(size int, parent *trieNode) *trieNode {
	return &trieNode{
		children: make([]*trieNode, size),
		parent:   parent,
	}
}

type trie struct {
	root   *trieNode
	size   int
	idxMap map[rune]int
}

const (
	lcLetters = "abcdefghijklmnopqrstuvwxyz"
	ucLetters = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
	numbers   = "0123456789"
)

func tr(charSet string) *trie {
	size := len(charSet)
	_assert(size > 0)
	idxMap := make(map[rune]int, size)
	for i, c := range charSet {
		if _, ok := idxMap[c]; ok {
			panic(nil)
		}
		idxMap[c] = i
	}
	return &trie{
		root:   newTrieNode(size, nil),
		size:   size,
		idxMap: idxMap,
	}
}

func (t *trie) insert(s string, cnt int) {
	_assert(cnt > 0)
	p := t.root
	for _, c := range s {
		p.subCnt += cnt
		idx := t.idxMap[c]
		if p.children[idx] == nil {
			p.children[idx] = newTrieNode(t.size, p)
		}
		p = p.children[idx]
	}
	p.curCnt += cnt
}

func (t *trie) search(s string) *trieNode {
	p := t.root
	for _, c := range s {
		if p = p.children[t.idxMap[c]]; p == nil {
			return nil
		}
	}
	return p
}

func (t *trie) delete(s string, cnt int) {

}

func (t *trie) clear(prefix string) {

}

type strHash struct {
	n, mod int
	a, b   []int
}

func sh(s string, p, mod int) *strHash {
	n := len(s)
	_assert(n > 0)
	a, b := vct(n+1, 0), vct(n+1, 0)
	b[0] = 1
	for i := 1; i <= n; i++ {
		a[i] = (a[i-1]*p + int(s[i-1])) % mod
		b[i] = b[i-1] * p % mod
	}
	return &strHash{
		n:   n,
		mod: mod,
		a:   a,
		b:   b,
	}
}

func (h *strHash) equal(l1, r1, l2, r2 int) bool {
	_assert(btw(l1, 0, h.n-1), btw(r1, l1, h.n-1), btw(l2, 0, h.n-1), btw(r2, l2, h.n-1), r1-l1 == r2-l2)
	return l1 == l2 || h.calc(l1, r1) == h.calc(l2, r2)
}

func (h *strHash) calc(l, r int) int {
	return (h.a[r+1] - h.a[l]*h.b[r-l+1]%h.mod + h.mod) % h.mod
}

type unionFind struct {
	size int
	a    []int
}

func uf(size int) *unionFind {
	a := vct(size, 0)
	for i := range a {
		a[i] = i
	}
	return &unionFind{
		size: size,
		a:    a,
	}
}

func (f *unionFind) find(x int) int {
	_assert(btw(x, 0, f.size-1))
	if f.a[x] != x {
		f.a[x] = f.find(f.a[x])
	}
	return f.a[x]
}

func (f *unionFind) union(x, y int) {
	_assert(btw(x, 0, f.size-1), btw(y, 0, f.size-1))
	f.a[f.find(x)] = f.find(y)
}

type segmentTree struct {
	l, r    int
	a, f, v []int
}

func st(l, r int, a []int) *segmentTree {
	_assert(l < r)
	size := (r - l + 1) << 2
	t := &segmentTree{
		l: l,
		r: r,
		a: a,
		f: vct(size, 0),
		v: vct(size, 0),
	}
	t._build(1, l, r)
	return t
}

func (t *segmentTree) _build(idx, l, r int) {
	if l == r {
		t.f[idx] = t.a[l]
		return
	}
	m, idx1, idx2 := l+(r-l)>>1, idx<<1, idx<<1+1
	t._build(idx1, l, m)
	t._build(idx2, m+1, r)
	t.f[idx] = t.f[idx1] + t.f[idx2]
}

func (t *segmentTree) insert(x, y, k int) {
	_assert(btw(x, t.l, t.r), btw(y, x, t.r))
	t._insert(1, t.l, t.r, x, y, k)
}

func (t *segmentTree) _insert(idx, l, r, x, y, k int) {
	if l == x && r == y {
		t.v[idx] += k
		return
	}
	t.f[idx] += (y - x + 1) * k
	m, idx1, idx2 := l+(r-l)>>1, idx<<1, idx<<1+1
	if y <= m {
		t._insert(idx1, l, m, x, y, k)
	} else if x > m {
		t._insert(idx2, m+1, r, x, y, k)
	} else {
		t._insert(idx1, l, m, x, m, k)
		t._insert(idx2, m+1, r, m+1, y, k)
	}
}

func (t *segmentTree) calc(x, y int) int {
	_assert(btw(x, t.l, t.r), btw(y, x, t.r))
	return t._calc(1, t.l, t.r, x, y, 0)
}

func (t *segmentTree) _calc(idx, l, r, x, y, p int) int {
	if p += t.v[idx]; l == x && r == y {
		return p*(y-x+1) + t.f[idx]
	}
	m, idx1, idx2 := l+(r-l)>>1, idx<<1, idx<<1+1
	if y <= m {
		return t._calc(idx1, l, m, x, y, p)
	}
	if x > m {
		return t._calc(idx2, m+1, r, x, y, p)
	}
	return t._calc(idx1, l, m, x, m, p) + t._calc(idx2, m+1, r, m+1, y, p)
}
