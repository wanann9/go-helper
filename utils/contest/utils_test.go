package contest

import (
	"math"
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
		{byte('0')}, {byte('9')}, {byte('a')},
	} {
		t.Log(isNumber(a.c))
	}
}

func Test_isLetter(t *testing.T) {
	type args struct {
		c byte
	}
	for _, a := range []*args{
		{byte('a')}, {byte('z')}, {byte('A')}, {byte('Z')}, {byte('0')},
	} {
		t.Log(isLetter(a.c))
	}
}

func Test_isLower(t *testing.T) {
	type args struct {
		c byte
	}
	for _, a := range []*args{
		{byte('a')}, {byte('z')}, {byte('A')}, {byte('Z')}, {byte('0')},
	} {
		t.Log(isLower(a.c))
	}
}

func Test_isUpper(t *testing.T) {
	type args struct {
		c byte
	}
	for _, a := range []*args{
		{byte('a')}, {byte('z')}, {byte('A')}, {byte('Z')}, {byte('0')},
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

func Test_pop(t *testing.T) {
	a := []int{0, 1, 2}
	t.Log(pop(&a))
	t.Log(a)
}

func Test_cpRvs(t *testing.T) {
	type args struct {
		a []int
	}
	for _, a := range []*args{
		{[]int{0, 1, 2}},
	} {
		t.Log(cpRvs(a.a))
		t.Log(a.a)
	}
}

func Test_cp(t *testing.T) {
	type args struct {
		a []int
	}
	for _, a := range []*args{
		{[]int{0, 1, 2}},
	} {
		t.Log(cp(a.a))
	}
}

func Test_unq(t *testing.T) {
	type args struct {
		a []int
	}
	for _, a := range []*args{
		{[]int{0, 0, 0, 1, 1, 2}},
	} {
		t.Log(unq(a.a))
	}
}

func Test_tp(t *testing.T) {
	type args struct {
		a []int
	}
	for _, a := range []*args{
		{[]int{0}},
		{[]int{0, 0}},
		{[]int{0, 1}},
		{[]int{1, 0}},
		{[]int{0, 1, 1}},
		{[]int{1, 0, 0}},
		{[]int{0, 1, 0}},
	} {
		t.Logf("%b", tp(a.a))
	}
}

func Test_bs(t *testing.T) {
	type args struct {
		a []int
		b int
		t byte
	}
	for _, a := range []*args{
		{[]int{}, 0, 0},
		{[]int{0}, 0, 0},
		{[]int{0}, 1, 0},
		{[]int{0, 0}, 1, 1},
		{[]int{0, 1, 1, 3}, 1, 3},
		{[]int{0, 1, 1, 3}, 2, 3},
		{[]int{0, 1, 1, 3}, 4, 3},
		{[]int{3, 1, 1, 0}, 1, 5},
		{[]int{3, 1, 1, 0}, 2, 5},
		{[]int{3, 1, 1, 0}, 4, 5},
	} {
		t.Log(bs(a.a, a.b, a.t))
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
	it := m.iteratorAt(m.Left())
	for it.prev(); it.next(); {
		t.Log(it.key(), it.value())
	}
	for it.prev() {
		t.Log(it.key(), it.value())
	}
}

func Test_treeSet(t *testing.T) {
	s1, s2, s3 := ts(cmpInt), ts(cmpInt), ts(rvsCmp(cmpInt))
	s1.Put(1, 3, 5)
	s2.Put(2, 3, 4, 5)
	t.Log(s1.intersection(s2).Values())
	t.Log(s1.union(s2).Values())
	t.Log(s1.difference(s2).Values())
	s3.Put(vector{1, 2}, vector{2, 3})
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

func Test_1(t *testing.T) {
	for x := int(1e7); x > 1; x-- {
		if isPrime(x) {
			t.Log(x)
			break
		}
	}
	for x := int(1e7); x <= math.MaxInt; x++ {
		if isPrime(x) {
			t.Log(x)
			break
		}
	}
}
