package contest

import "testing"

// 不超过x的最大质数
func Test_1(t *testing.T) {
	for x := int(1e7); x > 1; x-- {
		if isPrime(x) {
			t.Log(x)
			break
		}
	}
}
