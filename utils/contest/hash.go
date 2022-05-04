package contest

type hash struct {
	n, m int
	f    []pair
	a, b [][]int
}

var hashFactors = []pair{{137, 9999971}, {131, 9999973}, {127, 9999991}}

var hsh = func(n int, elm func(int) int, factors ...pair) *hash {
	v := vct(n, 0)
	for i := range v {
		v[i] = elm(i)
	}
	m := len(factors)
	a, b := mtx(n+1, m, 0), mtx(n+1, m, 0)
	b[0] = vct(m, 1)
	for i := 1; i <= n; i++ {
		for j, f := range factors {
			a[i][j] = (a[i-1][j]*f[0]%f[1] + v[i-1]%f[1]) % f[1]
			b[i][j] = b[i-1][j] * f[0] % f[1]
		}
	}
	return &hash{
		n: n,
		m: m,
		f: factors,
		a: a,
		b: b,
	}
}

func (h *hash) equal(h2 *hash, l, r, l2, r2 int) bool {
	for i := 0; i < h.m; i++ {
		if h._calc(i, l, r) != h2._calc(i, l2, r2) {
			return false
		}
	}
	return true
}

func (h *hash) _calc(i, l, r int) int {
	return (h.a[r+1][i] - h.a[l][i]*h.b[r-l+1][i]%h.f[i][1] + h.f[i][1]) % h.f[i][1]
}
