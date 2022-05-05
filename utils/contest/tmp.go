package contest

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
