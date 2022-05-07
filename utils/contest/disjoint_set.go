package main

type disjointSet struct {
	a, b []int
	n    int
}

var djs = func(n int) *disjointSet {
	a := vct(n, 0)
	for i := range a {
		a[i] = i
	}
	return &disjointSet{
		a: a,
		b: vct(n, 1),
		n: n,
	}
}

func (s *disjointSet) find(x int) int {
	if s.a[x] != x {
		s.a[x] = s.find(s.a[x])
	}
	return s.a[x]
}

func (s *disjointSet) unite(from, to int) bool {
	if from, to = s.find(from), s.find(to); from == to {
		return false
	}
	s.a[from] = to
	s.b[to] += s.b[from]
	s.n--
	return true
}

func (s *disjointSet) united(x, y int) bool {
	return s.find(x) == s.find(y)
}
