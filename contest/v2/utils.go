package main

import (
	"fmt"
	"strconv"
)

type char interface {
	~byte | ~rune
}

type integer interface {
	~int | ~int8 | ~int16 | ~int32 | ~int64 | ~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64
}

type float interface {
	~float32 | ~float64
}

type number interface {
	integer | float
}

type ordered interface {
	number | ~string
}

var prt, prf = fmt.Println, fmt.Printf

func s2i(s string, base int) int {
	rst, _ := strconv.ParseInt(s, base, 64)
	return int(rst)
}

func i2s(i, base int) string {
	return strconv.FormatInt(int64(i), base)
}

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

func isNumber[T char](c T) bool {
	return c >= '0' && c <= '9'
}

func isLetter[T char](c T) bool {
	return isLower(c) || isUpper(c)
}

func isLower[T char](c T) bool {
	return c >= 'a' && c <= 'z'
}

func isUpper[T char](c T) bool {
	return c >= 'A' && c <= 'Z'
}

func toLower[T char](c T) T {
	if isUpper(c) {
		return c ^ 32
	}
	return c
}

func toUpper[T char](c T) T {
	if isLower(c) {
		return c ^ 32
	}
	return c
}

func abs[T number](a T) T {
	if a >= 0 {
		return a
	}
	return -a
}

func min[T ordered](item0 T, items ...T) T {
	for _, item := range items {
		if item < item0 {
			item0 = item
		}
	}
	return item0
}

func max[T ordered](item0 T, items ...T) T {
	for _, item := range items {
		if item > item0 {
			item0 = item
		}
	}
	return item0
}

func pow(a, b, mod int) (rst int) {
	for rst = 1; b > 0; b >>= 1 {
		if b&1 != 0 {
			if rst *= a; mod > 0 {
				rst %= mod
			}
		}
		if a *= a; mod > 0 {
			a %= mod
		}
	}
	return
}

func gcd(a, b int) int {
	if a%b == 0 {
		return b
	}
	return gcd(b, a%b)
}

func lcm(a, b int) int {
	return a / gcd(a, b) * b
}

var c [][]int

func initC(n, mod int) {
	c = mtx(n+1, n+1, 0, false)
	for i := 0; i <= n; i++ {
		c[i][0] = 1
		for j := 1; j <= i; j++ {
			if c[i][j] = c[i-1][j-1] + c[i-1][j]; mod > 0 {
				c[i][j] %= mod
			}
		}
	}
}

func isPrime(n int) bool {
	if n <= 1 {
		return false
	}
	for i := 2; i*i <= n; i++ {
		if n%i == 0 {
			return false
		}
	}
	return true
}

func factor(n int) map[int]int {
	rst := make(map[int]int)
	for i := 2; i*i <= n; i++ {
		for ; n%i == 0; n /= i {
			rst[i]++
		}
	}
	if n > 1 {
		rst[n]++
	}
	return rst
}

func vct[T any](l int, val T, init bool) []T {
	v := make([]T, l)
	if init {
		for i := range v {
			v[i] = val
		}
	}
	return v
}

func mtx[T any](l1, l2 int, val T, init bool) [][]T {
	m := make([][]T, l1)
	for i := range m {
		m[i] = vct(l2, val, init)
	}
	return m
}

func cb[T any](l1, l2, l3 int, val T, init bool) [][][]T {
	c := make([][][]T, l1)
	for i := range c {
		c[i] = mtx(l2, l3, val, init)
	}
	return c
}

var (
	_, _                         = prt, prf
	_, _, _                      = s2i, i2s, b2i
	_, _, _, _                   = isNumber[byte], isLetter[byte], isLower[byte], isUpper[byte]
	_, _                         = toLower[byte], toUpper[byte]
	_, _, _, _, _, _, _, _, _, _ = abs[int], min[int], max[int], pow, gcd, lcm, c, initC, isPrime, factor
	_, _, _                      = vct[int], mtx[int], cb[int]
)

const mod int = 1e9 + 7

//type ListNode struct {
//	Val  int
//	Next *ListNode
//}

//type TreeNode struct {
//	Val         int
//	Left, Right *TreeNode
//}

//func init() {
//	initC(1000, 0)
//}
