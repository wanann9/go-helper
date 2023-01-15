package main

import "github.com/emirpasic/gods/utils"

type topK struct {
	*heap
	k   int
	cmp utils.Comparator
}

func tk(k int, cmp utils.Comparator) *topK {
	return &topK{
		heap: hp(cmp),
		k:    k,
		cmp:  cmp,
	}
}

func (t *topK) Push(items ...interface{}) {
	for _, item := range items {
		if t.Size() < t.k || t.cmp(item, t.Peek()) > 0 {
			if t.heap.Push(item); t.Size() > t.k {
				t.Pop()
			}
		}
	}
}
