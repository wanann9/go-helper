package contest

type trieNode struct {
	children       []*trieNode
	parent         *trieNode
	curCnt, subCnt int
}

var trn = func(size int, parent *trieNode) *trieNode {
	return &trieNode{
		children: make([]*trieNode, size),
		parent:   parent,
	}
}

type trie struct {
	root *trieNode
	size int
	idx  map[byte]int
}

const (
	lcLetters = "abcdefghijklmnopqrstuvwxyz"
	ucLetters = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
	numbers   = "0123456789"
)

var tr = func(charSet string) *trie {
	size := len(charSet)
	_assert("tr", size > 0)
	idx := make(map[byte]int, size)
	for i, c := range text(charSet) {
		if _, ok := idx[c]; ok {
			panic("tr")
		}
		idx[c] = i
	}
	return &trie{
		root: trn(size, nil),
		size: size,
		idx:  idx,
	}
}

func (t *trie) insert(s string, cnt int) {
	_assert("trie_insert", cnt > 0)
	p := t.root
	for _, c := range text(s) {
		p.subCnt += cnt
		idx := t.idx[c]
		if p.children[idx] == nil {
			p.children[idx] = trn(t.size, p)
		}
		p = p.children[idx]
	}
	p.curCnt += cnt
}

func (t *trie) search(s string) *trieNode {
	p := t.root
	for _, c := range text(s) {
		if p = p.children[t.idx[c]]; p == nil {
			return nil
		}
	}
	return p
}

func (t *trie) delete(s string, cnt int) {

}

func (t *trie) clear(prefix string) {

}

type unionFind struct {
	size int
	a    []int
}

var uf = func(size int) *unionFind {
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
	_assert("unionFind_find", x >= 0, x < f.size)
	if f.a[x] != x {
		f.a[x] = f.find(f.a[x])
	}
	return f.a[x]
}

func (f *unionFind) union(x, y int) {
	_assert("unionFind_union", x >= 0, x < f.size, y >= 0, y < f.size)
	f.a[f.find(x)] = f.find(y)
}

type segmentTree struct {
	l, r    int
	a, f, v []int
}

var st = func(l, r int, a []int) *segmentTree {
	_assert("st", l < r)
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
	_assert("segmentTree_insert", x >= t.l, x <= t.r, y >= x, y <= t.r)
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
	_assert("segmentTree_calc", x >= t.l, x <= t.r, y >= x, y <= t.r)
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
