package main

import (
	"bytes"
	"container/list"
	"fmt"
	"index/suffixarray"
	"math"
	"math/big"
	"math/bits"
	"sort"
	"strconv"
	"strings"

	"github.com/emirpasic/gods/sets/hashset"
	"github.com/emirpasic/gods/trees/binaryheap"
	"github.com/emirpasic/gods/utils"
)

var prt, prf = fmt.Println, fmt.Printf

func s2i(s string, base int) int {
	rst, _ := strconv.ParseInt(s, base, 64)
	return int(rst)
}

func i2s(i, base int) string {
	return strconv.FormatInt(int64(i), base)
}

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

func isNumber(c byte) bool {
	return c >= '0' && c <= '9'
}

func isLetter(c byte) bool {
	return isLower(c) || isUpper(c)
}

func isLower(c byte) bool {
	return c >= 'a' && c <= 'z'
}

func isUpper(c byte) bool {
	return c >= 'A' && c <= 'Z'
}

func toLower(c byte) byte {
	if isUpper(c) {
		return c ^ 32
	}
	return c
}

func toUpper(c byte) byte {
	if isLower(c) {
		return c ^ 32
	}
	return c
}

func abs(a int) int {
	if a >= 0 {
		return a
	}
	return -a
}

func min(nums ...int) int {
	rst := math.MaxInt
	for _, n := range nums {
		if n < rst {
			rst = n
		}
	}
	return rst
}

func max(nums ...int) int {
	rst := math.MinInt
	for _, n := range nums {
		if n > rst {
			rst = n
		}
	}
	return rst
}

func pow(a, b, mod int) (rst int) {
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

func gcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func lcm(a, b int) int {
	return a / gcd(a, b) * b
}

var c [][]int

func initC(n, mod int) {
	c = mtx(n+1, n+1, 0)
	for i := 0; i <= n; i++ {
		c[i][0] = 1
		for j := 1; j <= i; j++ {
			if c[i][j] = c[i-1][j-1] + c[i-1][j]; mod > 0 {
				c[i][j] %= mod
			}
		}
	}
}

var (
	isPrime []bool
	primes  []int
)

func initPrime(n int) {
	isPrime = vctBool(n+1, true)
	isPrime[0], isPrime[1] = false, false
	for i := 2; i <= n; i++ {
		if isPrime[i] {
			primes = append(primes, i)
		}
		for _, p := range primes {
			if p*i > n {
				break
			}
			isPrime[p*i] = false
			if i%p == 0 {
				break
			}
		}
	}
}

func factor(n int) map[int]int {
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

func flatten(n int) []int {
	s := i2s(n, 10)
	rst := vct(len(s), 0)
	for i, c := range s {
		rst[i] = int(c - '0')
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

func mtx(l1, l2, init int) [][]int {
	m := make([][]int, l1)
	for i := range m {
		m[i] = vct(l2, init)
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

func vctBool(l int, init bool) []bool {
	v := make([]bool, l)
	if init {
		for i := range v {
			v[i] = true
		}
	}
	return v
}

func mtxBool(l1, l2 int, init bool) [][]bool {
	m := make([][]bool, l1)
	for i := range m {
		m[i] = vctBool(l2, init)
	}
	return m
}

func cbBool(l1, l2, l3 int, init bool) [][][]bool {
	c := make([][][]bool, l1)
	for i := range c {
		c[i] = mtxBool(l2, l3, init)
	}
	return c
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

func rvsCmp(cmp utils.Comparator) utils.Comparator {
	return func(a, b interface{}) int { return -cmp(a, b) }
}

func sz(a interface{}) (int, int) {
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

func fd(l, r, i int, check func(int) bool) int {
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

func al(l, r int, check func(int) bool) bool {
	for i := l; i <= r; i++ {
		if !check(i) {
			return false
		}
	}
	return true
}

func an(l, r int, check func(int) bool) bool {
	for i := l; i <= r; i++ {
		if check(i) {
			return true
		}
	}
	return false
}

func lb(l, r int, check func(int) bool) int {
	for l+1 < r {
		if m := l + (r-l)>>1; check(m) {
			r = m
		} else {
			l = m
		}
	}
	return r
}

func ub(l, r int, check func(int) bool) int {
	for l+1 < r {
		if m := l + (r-l)>>1; check(m) {
			l = m
		} else {
			r = m
		}
	}
	return l
}

func cnt(l, r, i int, check func(int) bool) (rst int) {
	for j := l; j <= r; j++ {
		if rst += b2i(check(j)); i > 0 && rst == i {
			break
		}
	}
	return
}

func sm(l, r int, key func(int) int) (rst int) {
	for i := l; i <= r; i++ {
		rst += key(i)
	}
	return
}

func idxSort(n int, less func(i, j int) bool) []int {
	rst := vct(n, 0)
	for i := range rst {
		rst[i] = i
	}
	sort.Slice(rst, func(i, j int) bool { return less(rst[i], rst[j]) })
	return rst
}

// lis 返回以nums[i]为结尾的最长递增子序列长度
func lis(nums []int) []int {
	n := len(nums)
	rst := vct(n, 0)
	var a []int
	for i, num := range nums {
		j := lb(-1, len(a), func(j int) bool { return a[j] >= num })
		rst[i] = j + 1
		if j == len(a) {
			a = append(a, num)
		} else {
			a[j] = num
		}
	}
	return rst
}

var (
	drt  = []pair{{-1, 0}, {1, 0}, {0, -1}, {0, 1}}
	drt2 = []pair{{-1, 0}, {1, 0}, {0, -1}, {0, 1}, {-1, -1}, {-1, 1}, {1, -1}, {1, 1}}
)

func srd(m, n, i, j int, drt []pair) []pair {
	rst := make([]pair, 0, len(drt))
	for _, d := range drt {
		if x, y := i+d[0], j+d[1]; in(x, y, 0, 0, m-1, n-1) {
			rst = append(rst, pair{x, y})
		}
	}
	return rst
}

func in(i, j, x1, y1, x2, y2 int) bool {
	return i >= x1 && i <= x2 && j >= y1 && j <= y2
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

func child(n int, parent []int) ([][]int, int) {
	rst, root := make([][]int, n), -1
	for c, p := range parent {
		if p >= 0 {
			rst[p] = append(rst[p], c)
		} else {
			root = c
		}
	}
	return rst, root
}

func dijkstra(n int, g [][]pair, src int) []int {
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

func tpSort(n int, g [][]pair, id []int) []int {
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

func (v vector) copy() vector {
	rst := make(vector, len(v))
	copy(rst, v)
	return rst
}

func (v vector) reverse() vector {
	for i, j := 0, len(v)-1; i < j; i, j = i+1, j-1 {
		v[i], v[j] = v[j], v[i]
	}
	return v
}

func (v vector) sort(cmp utils.Comparator, stable bool) vector {
	if stable {
		sort.SliceStable(v, func(i, j int) bool { return cmp(v[i], v[j]) < 0 })
	} else {
		sort.Slice(v, func(i, j int) bool { return cmp(v[i], v[j]) < 0 })
	}
	return v
}

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

func (t text) copy() text {
	rst := make(text, len(t))
	copy(rst, t)
	return rst
}

func (t text) reverse() text {
	for i, j := 0, len(t)-1; i < j; i, j = i+1, j-1 {
		t[i], t[j] = t[j], t[i]
	}
	return t
}

func (t text) sort(cmp utils.Comparator, stable bool) text {
	if stable {
		sort.SliceStable(t, func(i, j int) bool { return cmp(t[i], t[j]) < 0 })
	} else {
		sort.Slice(t, func(i, j int) bool { return cmp(t[i], t[j]) < 0 })
	}
	return t
}

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

func hp(cmp utils.Comparator) *heap {
	return &heap{binaryheap.NewWith(cmp)}
}

func (h *heap) Pop() interface{} {
	rst, _ := h.Heap.Pop()
	return rst
}

func (h *heap) Peek() interface{} {
	rst, _ := h.Heap.Peek()
	return rst
}

const rbtNodeRed, rbtNodeBlack = false, true

type rbtNode struct {
	color               bool
	Key, Value          interface{}
	Left, Right, Parent *rbtNode
}

func (node *rbtNode) grandparent() *rbtNode {
	if node != nil && node.Parent != nil {
		return node.Parent.Parent
	}
	return nil
}

func (node *rbtNode) uncle() *rbtNode {
	if node == nil || node.Parent == nil || node.Parent.Parent == nil {
		return nil
	}
	return node.Parent.sibling()
}

func (node *rbtNode) sibling() *rbtNode {
	if node == nil || node.Parent == nil {
		return nil
	}
	if node == node.Parent.Left {
		return node.Parent.Right
	}
	return node.Parent.Left
}

func (node *rbtNode) maximumNode() *rbtNode {
	if node == nil {
		return nil
	}
	p := node
	for p.Right != nil {
		p = p.Right
	}
	return p
}

func (node *rbtNode) Size() int {
	if node == nil {
		return 0
	}
	size := 1
	if node.Left != nil {
		size += node.Left.Size()
	}
	if node.Right != nil {
		size += node.Right.Size()
	}
	return size
}

const rbtIterBegin, rbtIterBetween, rbtIterEnd byte = 0, 1, 2

type rbtIter struct {
	tree     *rbTree
	node     *rbtNode
	position byte
}

func (iterator *rbtIter) Next() bool {
	if iterator.position == rbtIterEnd {
		goto end
	}
	if iterator.position == rbtIterBegin {
		left := iterator.tree.Left()
		if left == nil {
			goto end
		}
		iterator.node = left
		goto between
	}
	if iterator.node.Right != nil {
		iterator.node = iterator.node.Right
		for iterator.node.Left != nil {
			iterator.node = iterator.node.Left
		}
		goto between
	}
	for iterator.node.Parent != nil {
		node := iterator.node
		iterator.node = iterator.node.Parent
		if node == iterator.node.Left {
			goto between
		}
	}

end:
	iterator.node = nil
	iterator.position = rbtIterEnd
	return false

between:
	iterator.position = rbtIterBetween
	return true
}

func (iterator *rbtIter) Prev() bool {
	if iterator.position == rbtIterBegin {
		goto begin
	}
	if iterator.position == rbtIterEnd {
		right := iterator.tree.Right()
		if right == nil {
			goto begin
		}
		iterator.node = right
		goto between
	}
	if iterator.node.Left != nil {
		iterator.node = iterator.node.Left
		for iterator.node.Right != nil {
			iterator.node = iterator.node.Right
		}
		goto between
	}
	for iterator.node.Parent != nil {
		node := iterator.node
		iterator.node = iterator.node.Parent
		if node == iterator.node.Right {
			goto between
		}
	}

begin:
	iterator.node = nil
	iterator.position = rbtIterBegin
	return false

between:
	iterator.position = rbtIterBetween
	return true
}

func (iterator *rbtIter) Value() interface{} {
	return iterator.node.Value
}

func (iterator *rbtIter) Key() interface{} {
	return iterator.node.Key
}

func (iterator *rbtIter) Node() *rbtNode {
	return iterator.node
}

func (iterator *rbtIter) Begin() {
	iterator.node = nil
	iterator.position = rbtIterBegin
}

func (iterator *rbtIter) End() {
	iterator.node = nil
	iterator.position = rbtIterEnd
}

func (iterator *rbtIter) First() bool {
	iterator.Begin()
	return iterator.Next()
}

func (iterator *rbtIter) Last() bool {
	iterator.End()
	return iterator.Prev()
}

func (iterator *rbtIter) NextTo(f func(key interface{}, value interface{}) bool) bool {
	for iterator.Next() {
		key, value := iterator.Key(), iterator.Value()
		if f(key, value) {
			return true
		}
	}
	return false
}

func (iterator *rbtIter) PrevTo(f func(key interface{}, value interface{}) bool) bool {
	for iterator.Prev() {
		key, value := iterator.Key(), iterator.Value()
		if f(key, value) {
			return true
		}
	}
	return false
}

type rbTree struct {
	size       int
	Root       *rbtNode
	Comparator utils.Comparator
}

func (tree *rbTree) Put(key interface{}, value interface{}) {
	var insertedNode *rbtNode
	if tree.Root == nil {
		// Assert key is of comparator's type for initial tree
		tree.Comparator(key, key)
		tree.Root = &rbtNode{Key: key, Value: value, color: rbtNodeRed}
		insertedNode = tree.Root
	} else {
		node := tree.Root
		loop := true
		for loop {
			compare := tree.Comparator(key, node.Key)
			switch {
			case compare == 0:
				node.Key = key
				node.Value = value
				return
			case compare < 0:
				if node.Left == nil {
					node.Left = &rbtNode{Key: key, Value: value, color: rbtNodeRed}
					insertedNode = node.Left
					loop = false
				} else {
					node = node.Left
				}
			case compare > 0:
				if node.Right == nil {
					node.Right = &rbtNode{Key: key, Value: value, color: rbtNodeRed}
					insertedNode = node.Right
					loop = false
				} else {
					node = node.Right
				}
			}
		}
		insertedNode.Parent = node
	}
	tree.insertCase1(insertedNode)
	tree.size++
}

func (tree *rbTree) Get(key interface{}) (value interface{}, found bool) {
	node := tree.lookup(key)
	if node != nil {
		return node.Value, true
	}
	return nil, false
}

func (tree *rbTree) GetNode(key interface{}) *rbtNode {
	return tree.lookup(key)
}

func (tree *rbTree) Remove(key interface{}) {
	tree.RemoveNode(tree.lookup(key))
}

func (tree *rbTree) RemoveNode(node *rbtNode) {
	var child *rbtNode
	if node == nil {
		return
	}
	if node.Left != nil && node.Right != nil {
		pred := node.Left.maximumNode()
		node.Key = pred.Key
		node.Value = pred.Value
		node = pred
	}
	if node.Left == nil || node.Right == nil {
		if node.Right == nil {
			child = node.Left
		} else {
			child = node.Right
		}
		if node.color == rbtNodeBlack {
			node.color = tree.nodeColor(child)
			tree.deleteCase1(node)
		}
		tree.replaceNode(node, child)
		if node.Parent == nil && child != nil {
			child.color = rbtNodeBlack
		}
	}
	tree.size--
}

func (tree *rbTree) Empty() bool {
	return tree.size == 0
}

func (tree *rbTree) Size() int {
	return tree.size
}

func (tree *rbTree) Clear() {
	tree.Root = nil
	tree.size = 0
}

func (tree *rbTree) Keys() []interface{} {
	keys := make([]interface{}, tree.size)
	it := tree.Iterator()
	for i := 0; it.Next(); i++ {
		keys[i] = it.Key()
	}
	return keys
}

func (tree *rbTree) Values() []interface{} {
	values := make([]interface{}, tree.size)
	it := tree.Iterator()
	for i := 0; it.Next(); i++ {
		values[i] = it.Value()
	}
	return values
}

func (tree *rbTree) Left() *rbtNode {
	var parent *rbtNode
	current := tree.Root
	for current != nil {
		parent = current
		current = current.Left
	}
	return parent
}

func (tree *rbTree) Right() *rbtNode {
	var parent *rbtNode
	current := tree.Root
	for current != nil {
		parent = current
		current = current.Right
	}
	return parent
}

func (tree *rbTree) Floor(key interface{}) (floor *rbtNode, found bool) {
	found = false
	node := tree.Root
	for node != nil {
		compare := tree.Comparator(key, node.Key)
		switch {
		case compare == 0:
			return node, true
		case compare < 0:
			node = node.Left
		case compare > 0:
			floor, found = node, true
			node = node.Right
		}
	}
	if found {
		return floor, true
	}
	return nil, false
}

func (tree *rbTree) Ceiling(key interface{}) (ceiling *rbtNode, found bool) {
	found = false
	node := tree.Root
	for node != nil {
		compare := tree.Comparator(key, node.Key)
		switch {
		case compare == 0:
			return node, true
		case compare < 0:
			ceiling, found = node, true
			node = node.Left
		case compare > 0:
			node = node.Right
		}
	}
	if found {
		return ceiling, true
	}
	return nil, false
}

func (tree *rbTree) Iterator() *rbtIter {
	return &rbtIter{tree: tree, node: nil, position: rbtIterBegin}
}

func (tree *rbTree) IteratorAt(node *rbtNode) *rbtIter {
	return &rbtIter{tree: tree, node: node, position: rbtIterBetween}
}

func (tree *rbTree) lookup(key interface{}) *rbtNode {
	node := tree.Root
	for node != nil {
		compare := tree.Comparator(key, node.Key)
		switch {
		case compare == 0:
			return node
		case compare < 0:
			node = node.Left
		case compare > 0:
			node = node.Right
		}
	}
	return nil
}

func (tree *rbTree) insertCase1(node *rbtNode) {
	if node.Parent == nil {
		node.color = rbtNodeBlack
	} else {
		tree.insertCase2(node)
	}
}

func (tree *rbTree) insertCase2(node *rbtNode) {
	if tree.nodeColor(node.Parent) == rbtNodeBlack {
		return
	}
	tree.insertCase3(node)
}

func (tree *rbTree) insertCase3(node *rbtNode) {
	uncle := node.uncle()
	if tree.nodeColor(uncle) == rbtNodeRed {
		node.Parent.color = rbtNodeBlack
		uncle.color = rbtNodeBlack
		node.grandparent().color = rbtNodeRed
		tree.insertCase1(node.grandparent())
	} else {
		tree.insertCase4(node)
	}
}

func (tree *rbTree) insertCase4(node *rbtNode) {
	grandparent := node.grandparent()
	if node == node.Parent.Right && node.Parent == grandparent.Left {
		tree.rotateLeft(node.Parent)
		node = node.Left
	} else if node == node.Parent.Left && node.Parent == grandparent.Right {
		tree.rotateRight(node.Parent)
		node = node.Right
	}
	tree.insertCase5(node)
}

func (tree *rbTree) insertCase5(node *rbtNode) {
	node.Parent.color = rbtNodeBlack
	grandparent := node.grandparent()
	grandparent.color = rbtNodeRed
	if node == node.Parent.Left && node.Parent == grandparent.Left {
		tree.rotateRight(grandparent)
	} else if node == node.Parent.Right && node.Parent == grandparent.Right {
		tree.rotateLeft(grandparent)
	}
}

func (tree *rbTree) deleteCase1(node *rbtNode) {
	if node.Parent == nil {
		return
	}
	tree.deleteCase2(node)
}

func (tree *rbTree) deleteCase2(node *rbtNode) {
	sibling := node.sibling()
	if tree.nodeColor(sibling) == rbtNodeRed {
		node.Parent.color = rbtNodeRed
		sibling.color = rbtNodeBlack
		if node == node.Parent.Left {
			tree.rotateLeft(node.Parent)
		} else {
			tree.rotateRight(node.Parent)
		}
	}
	tree.deleteCase3(node)
}

func (tree *rbTree) deleteCase3(node *rbtNode) {
	sibling := node.sibling()
	if tree.nodeColor(node.Parent) == rbtNodeBlack &&
		tree.nodeColor(sibling) == rbtNodeBlack &&
		tree.nodeColor(sibling.Left) == rbtNodeBlack &&
		tree.nodeColor(sibling.Right) == rbtNodeBlack {
		sibling.color = rbtNodeRed
		tree.deleteCase1(node.Parent)
	} else {
		tree.deleteCase4(node)
	}
}

func (tree *rbTree) deleteCase4(node *rbtNode) {
	sibling := node.sibling()
	if tree.nodeColor(node.Parent) == rbtNodeRed &&
		tree.nodeColor(sibling) == rbtNodeBlack &&
		tree.nodeColor(sibling.Left) == rbtNodeBlack &&
		tree.nodeColor(sibling.Right) == rbtNodeBlack {
		sibling.color = rbtNodeRed
		node.Parent.color = rbtNodeBlack
	} else {
		tree.deleteCase5(node)
	}
}

func (tree *rbTree) deleteCase5(node *rbtNode) {
	sibling := node.sibling()
	if node == node.Parent.Left &&
		tree.nodeColor(sibling) == rbtNodeBlack &&
		tree.nodeColor(sibling.Left) == rbtNodeRed &&
		tree.nodeColor(sibling.Right) == rbtNodeBlack {
		sibling.color = rbtNodeRed
		sibling.Left.color = rbtNodeBlack
		tree.rotateRight(sibling)
	} else if node == node.Parent.Right &&
		tree.nodeColor(sibling) == rbtNodeBlack &&
		tree.nodeColor(sibling.Right) == rbtNodeRed &&
		tree.nodeColor(sibling.Left) == rbtNodeBlack {
		sibling.color = rbtNodeRed
		sibling.Right.color = rbtNodeBlack
		tree.rotateLeft(sibling)
	}
	tree.deleteCase6(node)
}

func (tree *rbTree) deleteCase6(node *rbtNode) {
	sibling := node.sibling()
	sibling.color = tree.nodeColor(node.Parent)
	node.Parent.color = rbtNodeBlack
	if node == node.Parent.Left && tree.nodeColor(sibling.Right) == rbtNodeRed {
		sibling.Right.color = rbtNodeBlack
		tree.rotateLeft(node.Parent)
	} else if tree.nodeColor(sibling.Left) == rbtNodeRed {
		sibling.Left.color = rbtNodeBlack
		tree.rotateRight(node.Parent)
	}
}

func (tree *rbTree) rotateLeft(node *rbtNode) {
	right := node.Right
	tree.replaceNode(node, right)
	node.Right = right.Left
	if right.Left != nil {
		right.Left.Parent = node
	}
	right.Left = node
	node.Parent = right
}

func (tree *rbTree) rotateRight(node *rbtNode) {
	left := node.Left
	tree.replaceNode(node, left)
	node.Left = left.Right
	if left.Right != nil {
		left.Right.Parent = node
	}
	left.Right = node
	node.Parent = left
}

func (tree *rbTree) replaceNode(old *rbtNode, new *rbtNode) {
	if old.Parent == nil {
		tree.Root = new
	} else {
		if old == old.Parent.Left {
			old.Parent.Left = new
		} else {
			old.Parent.Right = new
		}
	}
	if new != nil {
		new.Parent = old.Parent
	}
}

func (*rbTree) nodeColor(node *rbtNode) bool {
	if node == nil {
		return rbtNodeBlack
	}
	return node.color
}

type treeMap struct {
	*rbTree
}

func tm(cmp utils.Comparator) *treeMap {
	return &treeMap{&rbTree{Comparator: cmp}}
}

func (m *treeMap) Floor(x interface{}) *rbtNode {
	rst, _ := m.rbTree.Floor(x)
	return rst
}

func (m *treeMap) Ceiling(x interface{}) *rbtNode {
	rst, _ := m.rbTree.Ceiling(x)
	return rst
}

type treeSet struct {
	*treeMap
}

func ts(cmp utils.Comparator) *treeSet {
	return &treeSet{tm(cmp)}
}

func (s *treeSet) Put(items ...interface{}) {
	for _, item := range items {
		s.rbTree.Put(item, struct{}{})
	}
}

func (s *treeSet) Remove(items ...interface{}) {
	for _, item := range items {
		s.rbTree.Remove(item)
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

func mts(cmp utils.Comparator) *multiSet {
	return &multiSet{
		treeSet: ts(func(a, b interface{}) int {
			aa, bb := a.(mtsItem), b.(mtsItem)
			if rst := cmp(aa.val, bb.val); rst != 0 {
				return rst
			}
			return aa.idx - bb.idx
		}),
		cnt: tm(cmp),
	}
}

func (s *multiSet) Put(items ...interface{}) {
	for _, item := range items {
		if node := s.cnt.GetNode(item); node != nil {
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
		if node := s.cnt.GetNode(item); node != nil {
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

func hs(a interface{}) *hashSet {
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

func dq() *deque {
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

var _ = []interface{}{
	big.NewInt, big.Int{},

	bits.Len, bits.Reverse, bits.OnesCount, bits.LeadingZeros, bits.TrailingZeros,

	bytes.Map, bytes.Join, bytes.Count, bytes.Repeat, bytes.Compare, bytes.Replace, bytes.EqualFold,
	bytes.ToLower, bytes.ToUpper, bytes.Fields, bytes.FieldsFunc, bytes.SplitN, bytes.SplitAfterN,
	bytes.HasPrefix, bytes.HasSuffix, bytes.Contains, bytes.ContainsAny,
	bytes.Index, bytes.IndexAny, bytes.IndexFunc, bytes.LastIndex, bytes.LastIndexAny, bytes.LastIndexFunc,
	bytes.Trim, bytes.TrimFunc, bytes.TrimPrefix, bytes.TrimSuffix,
	bytes.TrimLeft, bytes.TrimLeftFunc, bytes.TrimRight, bytes.TrimRightFunc,

	sort.Ints, sort.Float64s, sort.Strings, sort.Slice, sort.SliceStable,
	sort.IntsAreSorted, sort.Float64sAreSorted, sort.StringsAreSorted,

	strings.Map, strings.Join, strings.Count, strings.Repeat, strings.Compare, strings.Replace, strings.EqualFold,
	strings.ToLower, strings.ToUpper, strings.Fields, strings.FieldsFunc, strings.SplitN, strings.SplitAfterN,
	strings.HasPrefix, strings.HasSuffix, strings.Contains, strings.ContainsAny,
	strings.Index, strings.IndexAny, strings.IndexFunc, strings.LastIndex, strings.LastIndexAny, strings.LastIndexFunc,
	strings.Trim, strings.TrimFunc, strings.TrimPrefix, strings.TrimSuffix,
	strings.TrimLeft, strings.TrimLeftFunc, strings.TrimRight, strings.TrimRightFunc,

	suffixarray.New, suffixarray.Index{},

	prt, prf,
	s2i, i2s, b2i, isNumber, isLetter, isLower, isUpper, toLower, toUpper,
	abs, min, max, pow, gcd, lcm, c, initC, isPrime, primes, initPrime, factor, flatten,
	vct, mtx, cb, vctBool, mtxBool, cbBool,
	cmpInt, cmpInt64, cmpUint, cmpUint64, cmpByte, cmpRune, cmpFloat64, cmpBool, cmpString, cmpPair, cmpTriplet, rvsCmp,
	sz, fd, al, an, lb, ub, cnt, sm, idxSort, lis,
	drt, drt2, srd, in, ug, dg, child, dijkstra, tpSort,
	pair{}, triplet{}, vector{}, text{},
	heap{}, treeMap{}, treeSet{}, multiSet{}, hashSet{}, deque{},
	hp, tm, ts, mts, hs, dq,
}

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
//	initPrime(1e6)
//}
