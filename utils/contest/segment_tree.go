package main

type segmentTree struct {
	n     int
	a     []int
	nodes []smtNode
}

type smtNode struct {
	f, v int
}

func smt(a []int) *segmentTree {
	n := len(a)
	t := &segmentTree{
		n:     n,
		a:     a,
		nodes: make([]smtNode, n<<2+1),
	}
	t.build(1, 0, n-1)
	return t
}

func (t *segmentTree) build(i, l, r int) {
	if l == r {
		t.nodes[i].f = t.a[l]
		return
	}
	m, i1, i2 := l+(r-l)>>1, i<<1, i<<1+1
	t.build(i1, l, m)
	t.build(i2, m+1, r)
	t.nodes[i].f = t.nodes[i1].f + t.nodes[i2].f
}

func (t *segmentTree) update(x, y, k int) {
	t.update2(1, 0, t.n-1, x, y, k)
}

func (t *segmentTree) update2(i, l, r, x, y, k int) {
	if x <= l && y >= r {
		t.nodes[i].v += k
		return
	}
	m, i1, i2 := l+(r-l)>>1, i<<1, i<<1+1
	t.down(i, i1, i2, l, m, r)
	if x <= m {
		t.update2(i1, l, m, x, y, k)
	}
	if y > m {
		t.update2(i2, m+1, r, x, y, k)
	}
	t.up(i, i1, i2, l, m, r)
}

func (t *segmentTree) calc(x, y int) int {
	return t.calc2(1, 0, t.n-1, x, y)
}

func (t *segmentTree) calc2(i, l, r, x, y int) (rst int) {
	if x <= l && y >= r {
		return t.nodes[i].f + t.nodes[i].v*(r-l+1)
	}
	m, i1, i2 := l+(r-l)>>1, i<<1, i<<1+1
	t.down(i, i1, i2, l, m, r)
	if x <= m {
		rst += t.calc2(i1, l, m, x, y)
	}
	if y > m {
		rst += t.calc2(i2, m+1, r, x, y)
	}
	t.up(i, i1, i2, l, m, r)
	return
}

func (t *segmentTree) down(i, i1, i2, l, m, r int) {
	if v := t.nodes[i].v; v != 0 {
		t.nodes[i1].v += v
		t.nodes[i2].v += v
		t.nodes[i].v = 0
	}
}

func (t *segmentTree) up(i, i1, i2, l, m, r int) {
	t.nodes[i].f = t.nodes[i1].f + t.nodes[i1].v*(m-l+1) + t.nodes[i2].f + t.nodes[i2].v*(r-m)
}
