package contest

type trieNode struct {
	children       []*trieNode
	parent         *trieNode
	curCnt, subCnt int
}

var trn = func(n int, parent *trieNode) *trieNode {
	return &trieNode{
		children: make([]*trieNode, n),
		parent:   parent,
	}
}

type trie struct {
	root *trieNode
	n    int
	idx  map[byte]int
}

const (
	numbers   = "0123456789"
	letters   = lcLetters + ucLetters
	lcLetters = "abcdefghijklmnopqrstuvwxyz"
	ucLetters = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
)

var tr = func(charSet string) *trie {
	n := len(charSet)
	idx := make(map[byte]int, n)
	for i, c := range text(charSet) {
		idx[c] = i
	}
	return &trie{
		root: trn(n, nil),
		n:    n,
		idx:  idx,
	}
}

func (t *trie) insert(s string, cnt int) *trieNode {
	p := t.root
	for _, c := range text(s) {
		idx := t.idx[c]
		if p.subCnt += cnt; p.children[idx] == nil {
			p.children[idx] = trn(t.n, p)
		}
		p = p.children[idx]
	}
	p.curCnt += cnt
	return p
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

func (t *trie) delete(s string, cnt int) (*trieNode, int) {
	p := t.search(s)
	if p == nil {
		return nil, 0
	}
	if cnt < 0 || cnt > p.curCnt {
		cnt = p.curCnt
	}
	if cnt == 0 {
		return p, 0
	}
	p.curCnt -= cnt
	for q := p.parent; q != nil; q = q.parent {
		q.subCnt -= cnt
	}
	return p, cnt
}

type trieNode01 struct {
	children       [2]*trieNode01
	parent         *trieNode01
	curCnt, subCnt int
	//min            int
}

var trn01 = func(parent *trieNode01) *trieNode01 {
	return &trieNode01{
		parent: parent,
		//min:    math.MaxInt,
	}
}

type trie01 struct {
	root *trieNode01
	bits int
}

var tr01 = func(bits int) *trie01 {
	return &trie01{
		root: trn01(nil),
		bits: bits,
	}
}

func (t *trie01) _parse(n int) []int {
	rst := vct(t.bits, 0)
	for i := t.bits - 1; n > 0; n, i = n>>1, i-1 {
		rst[i] = n & 1
	}
	return rst
}

func (t *trie01) insert(n, cnt int) *trieNode01 {
	p := t.root
	for _, i := range t._parse(n) {
		if p.subCnt += cnt; p.children[i] == nil {
			p.children[i] = trn01(p)
		}
		p = p.children[i]
		//p.min = min(p.min, n)
	}
	p.curCnt += cnt
	return p
}

func (t *trie01) search(n int) *trieNode01 {
	p := t.root
	for _, i := range t._parse(n) {
		if p = p.children[i]; p == nil {
			return nil
		}
	}
	return p
}

func (t *trie01) delete(n, cnt int) (*trieNode01, int) {
	p := t.search(n)
	if p == nil {
		return nil, 0
	}
	if cnt < 0 || cnt > p.curCnt {
		cnt = p.curCnt
	}
	if cnt == 0 {
		return p, 0
	}
	p.curCnt -= cnt
	for q := p.parent; q != nil; q = q.parent {
		q.subCnt -= cnt
	}
	return p, cnt
}

func (t *trie01) query(n int) (p *trieNode01, a int) {
	if p, a = t.root, 0; p.subCnt == 0 {
		return nil, 0
	}
	for _, i := range t._parse(n) {
		j := i ^ 1
		if q := p.children[j]; q == nil || q.curCnt+q.subCnt == 0 {
			j = i
		}
		p, a = p.children[j], a<<1+j
	}
	return
}

//func (t *trie01) query2(n, m int) (p *trieNode01, a int) {
//	if p, a = t.root, 0; p.subCnt == 0 {
//		return nil, 0
//	}
//	for _, i := range t._parse(n) {
//		j := i ^ 1
//		if q := p.children[j]; q == nil || q.min > m {
//			if j = i; p.children[j].min > m {
//				return nil, 0
//			}
//		}
//		p, a = p.children[j], a<<1+j
//	}
//	return
//}
