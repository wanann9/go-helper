package main

import (
	"fmt"
	"math"
)

func main() {
	for x := int(1e7); x > 1; x-- {
		if isPrime(x) {
			fmt.Println(x)
			break
		}
	}
	for x := int(1e7); x <= math.MaxInt; x++ {
		if isPrime(x) {
			fmt.Println(x)
			break
		}
	}
}
