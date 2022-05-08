package main

import "testing"

func Test_hash(t *testing.T) {
	v1, v2 := []int{0, 1, 2, 3, 1, 2, 3}, []int{2, 3, 1, 2, 0, 1}
	h1 := hsh(len(v1), func(i int) int { return v1[i] }, hashFactors...)
	h2 := hsh(len(v2), func(i int) int { return v2[i] }, hashFactors...)
	t.Log(h1.equal(h1, 1, 3, 4, 6))
	t.Log(h1.equal(h1, 0, 3, 3, 6))
	t.Log(h1.equal(h2, 2, 5, 0, 3))
	t.Log(h1.equal(h2, 0, 1, 4, 5))
	t.Log(h1.equal(h2, 1, 6, 0, 5))
}
