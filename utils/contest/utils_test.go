package contest

import (
	"math"
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
		a interface{}
	}
	for _, a := range []*args{
		{byte('0')}, {byte('9')}, {byte('a')},
		{'0'}, {'9'}, {'a'},
	} {
		t.Log(isNumber(a.a))
	}
}

func Test_isLetter(t *testing.T) {
	type args struct {
		a interface{}
	}
	for _, a := range []*args{
		{byte('a')}, {byte('z')}, {byte('A')}, {byte('Z')}, {byte('0')},
		{'a'}, {'z'}, {'A'}, {'Z'}, {'0'},
	} {
		t.Log(isLetter(a.a))
	}
}

func Test_isLower(t *testing.T) {
	type args struct {
		a interface{}
	}
	for _, a := range []*args{
		{byte('a')}, {byte('z')}, {byte('A')}, {byte('Z')}, {byte('0')},
		{'a'}, {'z'}, {'A'}, {'Z'}, {'0'},
	} {
		t.Log(isLower(a.a))
	}
}

func Test_isUpper(t *testing.T) {
	type args struct {
		a interface{}
	}
	for _, a := range []*args{
		{byte('a')}, {byte('z')}, {byte('A')}, {byte('Z')}, {byte('0')},
		{'a'}, {'z'}, {'A'}, {'Z'}, {'0'},
	} {
		t.Log(isUpper(a.a))
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
	n, mod := 6, 0
	c = mtx(n+1, n+1, 0)
	for i := 0; i <= n; i++ {
		c[i][0] = 1
		for j := 1; j <= i; j++ {
			if c[i][j] = c[i-1][j-1] + c[i-1][j]; mod > 1 {
				c[i][j] %= mod
			}
		}
	}
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
		drt        []vector
	}
	for _, a := range []*args{
		{2, 2, 0, 0, drt}, {2, 2, 0, 0, drt2},
	} {
		t.Log(srd(a.m, a.n, a.i, a.j, a.drt))
	}
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
