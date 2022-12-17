package main

import "testing"

func Test_topK(t *testing.T) {
	topK := tk(3, cmpInt)
	for i := 0; i < 5; i++ {
		topK.Push(i)
		t.Log(topK)
	}
}
