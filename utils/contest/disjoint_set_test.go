package contest

import (
	"math/rand"
	"testing"
)

func Test_disjointSet(t *testing.T) {
	s := djs(10)
	t.Log(s.a)
	for i, j := range rand.Perm(10) {
		s.unite(i, j)
		t.Log(i, j, s.a)
	}
	for i := 0; i < 10; i++ {
		t.Log(i, s.find(i))
		t.Log(s.a)
	}
}
