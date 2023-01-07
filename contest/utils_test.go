package main

import (
	"math/rand"
	"testing"
)

func Test_s2i(t *testing.T) {
	type args struct {
		s    string
		base int
	}
	for _, a := range []*args{
		{"10", 10}, {"10", 2}, {"", 10},
	} {
		t.Log(s2i(a.s, a.base))
	}
}

func Test_i2s(t *testing.T) {
	type args struct {
		i, base int
	}
	for _, a := range []*args{
		{10, 10}, {2, 2},
	} {
		t.Log(i2s(a.i, a.base))
	}
}

func Test_b2i(t *testing.T) {
	type args struct {
		b bool
	}
	for _, a := range []*args{
		{false}, {true},
	} {
		t.Log(b2i(a.b))
	}
}

func Test_isNumber(t *testing.T) {
	type args struct {
		c byte
	}
	for _, a := range []*args{
		{'0'}, {'9'}, {'a'},
	} {
		t.Log(isNumber(a.c))
	}
}

func Test_isLetter(t *testing.T) {
	type args struct {
		c byte
	}
	for _, a := range []*args{
		{'a'}, {'z'}, {'A'}, {'Z'}, {'0'},
	} {
		t.Log(isLetter(a.c))
	}
}

func Test_isLower(t *testing.T) {
	type args struct {
		c byte
	}
	for _, a := range []*args{
		{'a'}, {'z'}, {'A'}, {'Z'}, {'0'},
	} {
		t.Log(isLower(a.c))
	}
}

func Test_isUpper(t *testing.T) {
	type args struct {
		c byte
	}
	for _, a := range []*args{
		{'a'}, {'z'}, {'A'}, {'Z'}, {'0'},
	} {
		t.Log(isUpper(a.c))
	}
}

func Test_toLower(t *testing.T) {
	for _, c := range "azAZ." {
		t.Logf("%c", toLower(byte(c)))
	}
}

func Test_toUpper(t *testing.T) {
	for _, c := range "azAZ." {
		t.Logf("%c", toUpper(byte(c)))
	}
}

func Test_abs(t *testing.T) {
	type args struct {
		a int
	}
	for _, a := range []*args{
		{2}, {0}, {-2},
	} {
		t.Log(abs(a.a))
	}
}

func Test_min(t *testing.T) {
	type args struct {
		nums []int
	}
	for _, a := range []*args{
		{[]int{0, 1, 2}},
	} {
		t.Log(min(a.nums...))
	}
}

func Test_max(t *testing.T) {
	type args struct {
		nums []int
	}
	for _, a := range []*args{
		{[]int{0, 1, 2}},
	} {
		t.Log(max(a.nums...))
	}
}

func Test_pow(t *testing.T) {
	type args struct {
		a, b, mod int
	}
	for _, a := range []*args{
		{0, 1, 0}, {1, 0, 0}, {-1, 0, 0}, {-1, 1, 0},
		{2, 30, 0}, {-2, 31, 0}, {2, 255, mod}, {-2, 255, mod},
	} {
		t.Log(pow(a.a, a.b, a.mod))
	}
}

func Test_gcd(t *testing.T) {
	type args struct {
		a, b int
	}
	for _, a := range []*args{
		{1, 1}, {1, 2}, {18, 24},
	} {
		t.Log(gcd(a.a, a.b))
	}
}

func Test_lcm(t *testing.T) {
	type args struct {
		a, b int
	}
	for _, a := range []*args{
		{1, 1}, {1, 2}, {18, 24},
	} {
		t.Log(lcm(a.a, a.b))
	}
}

func Test_c(t *testing.T) {
	initC(6, 0)
	t.Log(c)
}

func Test_isPrime(t *testing.T) {
	type args struct {
		n int
	}
	for _, a := range []*args{
		{0}, {1}, {2}, {3}, {4}, {1 << 30},
	} {
		t.Log(isPrime(a.n))
	}
}

func Test_factor(t *testing.T) {
	type args struct {
		n int
	}
	for _, a := range []*args{
		{0}, {1}, {2}, {12}, {1 << 30},
	} {
		t.Log(factor(a.n))
	}
}

func Test_text_split(t *testing.T) {
	type args struct {
		s, charSet string
	}
	for _, a := range []*args{
		{"0, 1 23", " ,"},
	} {
		t.Log(text(a.s).split(a.charSet))
	}
}

func Test_srd(t *testing.T) {
	type args struct {
		m, n, i, j int
		drt        []pair
	}
	for _, a := range []*args{
		{2, 2, 0, 0, drt}, {2, 2, 0, 0, drt2},
	} {
		t.Log(srd(a.m, a.n, a.i, a.j, a.drt))
	}
}

func Test_treeMap(t *testing.T) {
	m := tm(cmpInt)
	for _, n := range rand.Perm(10) {
		m.Put(n, 10-n)
	}
	t.Log(m.Left(), m.Right())
	it := m.IteratorAt(m.Left())
	for it.Prev(); it.Next(); {
		t.Log(it.Key(), it.Value())
	}
	for it.Prev() {
		t.Log(it.Key(), it.Value())
	}
}

func Test_treeSet(t *testing.T) {
	s1, s2, s3 := ts(cmpInt), ts(cmpInt), ts(rvsCmp(cmpPair))
	s1.Put(1, 3, 5)
	s2.Put(2, 3, 4, 5)
	t.Log(s1.intersection(s2).Values())
	t.Log(s1.union(s2).Values())
	t.Log(s1.difference(s2).Values())
	s3.Put(pair{1, 2}, pair{2, 3})
	t.Log(s3.Values())
}

func Test_multiSet(t *testing.T) {
	s := mts(cmpPair)
	for i := 0; i < 20; i++ {
		s.Put(pair{i % 10, 10 - i%10})
	}
	t.Log(s.Values(), s.cnt.Values())
	s.Remove(pair{0, 10}, pair{1, 9}, pair{1, 8})
	s.removeAll(pair{2, 8}, pair{3, 7}, pair{3, 6})
	t.Log(s.Values(), s.cnt.Values())
}

func Test_hashSet(t *testing.T) {
	s1, s2 := hs([]pair{{0, 0}, {0, 1}}), hs([]pair{{0, 1}, {1, 0}})
	t.Log(s1.intersection(s2))
	t.Log(s1.union(s2))
	t.Log(s1.difference(s2))
}

func Test_idxSort(t *testing.T) {
	a := []int{1, 3, 2, 4}
	t.Log(idxSort(4, func(i, j int) bool { return a[i] < a[j] }))
}

func Test_lis(t *testing.T) {
	t.Log(lis([]int{0, 4, 2, 1, 5, 3, 6, 8, 7, 9}))
}
