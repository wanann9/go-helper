package main

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

var gcd = func(a, b int) int {
	for ; a%b != 0; a, b = b, a%b {
	}
	return b
}

var lcm = func(a, b int) int {
	return a / gcd(a, b) * b
}

var c [][]int

var initC = func(n, mod int) {
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
	switch a := a.(type) {
	case [][]int:
		return len(a), len(a[0])
	case [][]int64:
		return len(a), len(a[0])
	case [][]uint:
		return len(a), len(a[0])
	case [][]uint64:
		return len(a), len(a[0])
	case [][]byte:
		return len(a), len(a[0])
	case [][]rune:
		return len(a), len(a[0])
	case [][]float64:
		return len(a), len(a[0])
	case [][]bool:
		return len(a), len(a[0])
	case [][]string:
		return len(a), len(a[0])
	case []string:
		return len(a), len(a[0])
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

var rvs = func(a []int) {
	for i, j := 0, len(a)-1; i < j; i, j = i+1, j-1 {
		a[i], a[j] = a[j], a[i]
	}
}

var cpRvs = func(a []int) []int {
	rst := cp(a)
	rvs(rst)
	return rst
}

var cp = func(a []int) []int {
	rst := vct(len(a), 0)
	copy(rst, a)
	return rst
}

var unq = func(a []int) []int {
	rst := make([]int, 0, len(a))
	for i, n := range a {
		if i == 0 || n != a[i-1] {
			rst = append(rst, n)
		}
	}
	return rst
}

var (
	cmpInt     = utils.IntComparator
	cmpInt64   = utils.Int64Comparator
	cmpUint    = utils.UIntComparator
	cmpUint64  = utils.UInt64Comparator
	cmpByte    = utils.ByteComparator
	cmpRune    = utils.RuneComparator
	cmpFloat64 = utils.Float64Comparator
	cmpBool    = func(a, b interface{}) int { return b2i(a.(bool)) - b2i(b.(bool)) }
	cmpString  = utils.StringComparator
	cmpPair    = func(a, b interface{}) int {
		aa, bb := a.(pair), b.(pair)
		for i := 0; i < 2; i++ {
			if rst := cmpInt(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return 0
	}
	cmpTriplet = func(a, b interface{}) int {
		aa, bb := a.(triplet), b.(triplet)
		for i := 0; i < 3; i++ {
			if rst := cmpInt(aa[i], bb[i]); rst != 0 {
				return rst
			}
		}
		return 0
	}
)

var rvsCmp = func(cmp utils.Comparator) utils.Comparator {
	return func(a, b interface{}) int { return -cmp(a, b) }
}

const (
	et byte = 1 << iota
	lt
	gt
	lgt = lt | gt
)

var tp = func(a []int) (rst byte) {
	for i := 1; i < len(a); i++ {
		rst |= tp2(a[i-1], a[i], cmpInt)
	}
	return
}

var tp2 = func(a, b interface{}, cmp utils.Comparator) byte {
	if rst := cmp(a, b); rst == 0 {
		return et
	} else if rst < 0 {
		return lt
	}
	return gt
}

var bs = func(a []int, b int, t byte) int {
	check := func(i int) bool { return tp2(a[i], b, cmpInt)&t&lgt == 0 }
	if i := lb(-1, len(a), check); i >= 0 && i < len(a) && cmpInt(a[i], b) == 0 {
		return i
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
	dist, visited, h := vct(n, -1), vctBool(n, false), hp(cmpPair)
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

type tmIterator struct {
	tree *redblacktree.Tree
	node *redblacktree.Node
	pos  byte
}

const (
	tmIterBegin byte = iota
	tmIterBetween
	tmIterEnd
)

var tmIter = func(tree *redblacktree.Tree, node *redblacktree.Node, pos byte) *tmIterator {
	return &tmIterator{
		tree: tree,
		node: node,
		pos:  pos,
	}
}

func (it *tmIterator) next() bool {
	if it.pos == tmIterEnd {
		goto end
	}
	if it.pos == tmIterBegin {
		left := it.tree.Left()
		if left == nil {
			goto end
		}
		it.node = left
		goto between
	}
	if it.node.Right != nil {
		it.node = it.node.Right
		for it.node.Left != nil {
			it.node = it.node.Left
		}
		goto between
	}
	for it.node.Parent != nil {
		node := it.node
		it.node = it.node.Parent
		if node == it.node.Left {
			goto between
		}
	}
end:
	it.end()
	return false
between:
	it.pos = tmIterBetween
	return true
}

func (it *tmIterator) prev() bool {
	if it.pos == tmIterBegin {
		goto begin
	}
	if it.pos == tmIterEnd {
		right := it.tree.Right()
		if right == nil {
			goto begin
		}
		it.node = right
		goto between
	}
	if it.node.Left != nil {
		it.node = it.node.Left
		for it.node.Right != nil {
			it.node = it.node.Right
		}
		goto between
	}
	for it.node.Parent != nil {
		node := it.node
		it.node = it.node.Parent
		if node == it.node.Right {
			goto between
		}
	}
begin:
	it.begin()
	return false
between:
	it.pos = tmIterBetween
	return true
}

func (it *tmIterator) key() interface{} {
	return it.node.Key
}

func (it *tmIterator) value() interface{} {
	return it.node.Value
}

func (it *tmIterator) begin() {
	it.node, it.pos = nil, tmIterBegin
}

func (it *tmIterator) end() {
	it.node, it.pos = nil, tmIterEnd
}

func (it *tmIterator) first() bool {
	it.begin()
	return it.next()
}

func (it *tmIterator) last() bool {
	it.end()
	return it.prev()
}

func (it *tmIterator) nextTo(f func(key interface{}, value interface{}) bool) bool {
	for it.next() {
		if f(it.key(), it.value()) {
			return true
		}
	}
	return false
}

func (it *tmIterator) prevTo(f func(key interface{}, value interface{}) bool) bool {
	for it.prev() {
		if f(it.key(), it.value()) {
			return true
		}
	}
	return false
}

type treeMap struct {
	*redblacktree.Tree
}

var tm = func(comparator utils.Comparator) *treeMap {
	return &treeMap{redblacktree.NewWith(comparator)}
}

func (m *treeMap) getNode(key interface{}) *redblacktree.Node {
	for p := m.Root; p != nil; {
		if rst := m.Comparator(key, p.Key); rst == 0 {
			return p
		} else if rst < 0 {
			p = p.Left
		} else {
			p = p.Right
		}
	}
	return nil
}

func (m *treeMap) iterator() *tmIterator {
	return tmIter(m.Tree, nil, tmIterBegin)
}

func (m *treeMap) iteratorAt(node *redblacktree.Node) *tmIterator {
	return tmIter(m.Tree, node, tmIterBetween)
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

type mtsItem struct {
	val interface{}
	idx int
}

var mts = func(comparator utils.Comparator) *multiSet {
	return &multiSet{
		treeSet: ts(func(a, b interface{}) int {
			aa, bb := a.(mtsItem), b.(mtsItem)
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
		if node := s.cnt.getNode(item); node != nil {
			cnt := node.Value.(int)
			s.treeSet.Put(mtsItem{item, cnt})
			node.Value = cnt + 1
		} else {
			s.treeSet.Put(mtsItem{item, 0})
			s.cnt.Put(item, 1)
		}
	}
}

func (s *multiSet) Remove(items ...interface{}) {
	for _, item := range items {
		if node := s.cnt.getNode(item); node != nil {
			cnt := node.Value.(int)
			if cnt--; cnt == 0 {
				s.cnt.Remove(item)
			} else {
				node.Value = cnt
			}
			s.treeSet.Remove(mtsItem{item, cnt})
		}
	}
}

func (s *multiSet) removeAll(items ...interface{}) {
	for _, item := range items {
		if val, found := s.cnt.Get(item); found {
			s.cnt.Remove(item)
			cnt := val.(int)
			for cnt--; cnt >= 0; cnt-- {
				s.treeSet.Remove(mtsItem{item, cnt})
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
		rst[i] = item.(mtsItem).val
	}
	return rst
}

func (s *multiSet) min() interface{} {
	return s.treeSet.min().(mtsItem).val
}

func (s *multiSet) max() interface{} {
	return s.treeSet.max().(mtsItem).val
}

func (s *multiSet) floor(x interface{}) interface{} {
	if item := s.treeSet.floor(mtsItem{x, 0}); item != nil {
		return item.(mtsItem).val
	}
	return nil
}

func (s *multiSet) ceiling(x interface{}) interface{} {
	if item := s.treeSet.ceiling(mtsItem{x, 0}); item != nil {
		return item.(mtsItem).val
	}
	return nil
}

type hashSet struct {
	*hashset.Set
}

var hs = func(a interface{}) *hashSet {
	s := &hashSet{hashset.New()}
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

func (s *hashSet) intersection(another *hashSet) *hashSet {
	rst := hs(nil)
	for _, item := range s.Values() {
		if another.Contains(item) {
			rst.Add(item)
		}
	}
	return rst
}

func (s *hashSet) union(another *hashSet) *hashSet {
	rst := hs(nil)
	rst.Add(s.Values()...)
	rst.Add(another.Values()...)
	return rst
}

func (s *hashSet) difference(another *hashSet) *hashSet {
	rst := hs(nil)
	for _, item := range s.Values() {
		if !another.Contains(item) {
			rst.Add(item)
		}
	}
	return rst
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
	_             = big.NewInt
	_             = bits.Len
	_             = bits.Reverse
	_             = bits.OnesCount
	_, _          = bits.LeadingZeros, bits.TrailingZeros
	_, _, _, _, _ = sort.Ints, sort.Float64s, sort.Strings, sort.Slice, sort.SliceStable
	_, _, _       = sort.IntsAreSorted, sort.Float64sAreSorted, sort.StringsAreSorted
	_             = strings.Map
	_             = strings.Join
	_             = strings.Count
	_             = strings.Repeat
	_             = strings.Replace
	_             = strings.EqualFold
	_, _          = strings.ToLower, strings.ToUpper
	_, _          = strings.SplitN, strings.SplitAfterN
	_, _          = strings.HasPrefix, strings.HasSuffix
	_, _          = strings.Contains, strings.ContainsAny
	_, _, _       = strings.Index, strings.IndexAny, strings.IndexFunc
	_, _, _       = strings.LastIndex, strings.LastIndexAny, strings.LastIndexFunc
	_, _, _, _    = strings.Trim, strings.TrimFunc, strings.TrimPrefix, strings.TrimSuffix
	_, _, _, _    = strings.TrimLeft, strings.TrimLeftFunc, strings.TrimRight, strings.TrimRightFunc

	_, _                            = prt, prf
	_, _, _                         = s2i, i2s, b2i
	_, _, _, _, _, _                = isNumber, isLetter, isLower, isUpper, toLower, toUpper
	_, _, _, _, _, _, _, _, _, _    = abs, min, max, pow, gcd, lcm, c, initC, isPrime, factor
	_, _, _, _, _, _                = vct, mtx, cb, vctBool, mtxBool, cbBool
	_, _, _, _, _, _, _             = sz, pop, elm, rvs, cpRvs, cp, unq
	_, _, _, _, _, _                = cmpInt, cmpInt64, cmpUint, cmpUint64, cmpByte, cmpRune
	_, _, _, _, _, _                = cmpFloat64, cmpBool, cmpString, cmpPair, cmpTriplet, rvsCmp
	_, _, _, _, _, _, _, _, _, _, _ = et, lt, gt, lgt, tp, tp2, bs, fd, lb, ub, cnt
	_, _, _, _, _, _, _, _, _       = drt, drt2, srd, in, ug, dg, child, dijkstra, tpSort
	_, _, _, _                      = pair{}, triplet{}, vector{}, text{}
	_, _, _, _, _, _, _             = heap{}, tmIterator{}, treeMap{}, treeSet{}, multiSet{}, hashSet{}, deque{}
	_, _, _, _, _, _, _, _, _, _    = hp, tmIterBegin, tmIterBetween, tmIterEnd, tmIter, tm, ts, mts, hs, dq
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
//	initC(1000, 0)
//}
