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
