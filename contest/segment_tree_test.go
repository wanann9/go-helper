package main

import "testing"

func Test_segmentTree(t *testing.T) {
	tree := smt([]int{1, 2, 3, 4, 5})
	t.Log(tree)
	tree.update(0, 4, 1)
	t.Log(tree)
	tree.update(0, 2, 1)
	t.Log(tree)
	t.Log(tree.calc(1, 3))
	t.Log(tree)
}

func Test_segmentTree2(t *testing.T) {
	tree := smt2(0, 4)
	tree.update(0, 4, 1)
	tree.update(1, 4, 1)
	tree.update(2, 4, 1)
	tree.update(3, 4, 1)
	tree.update(4, 4, 1)
	t.Log(tree.smtNode2)
	tree.update(0, 4, 1)
	t.Log(tree.smtNode2)
	tree.update(0, 2, 1)
	t.Log(tree.smtNode2)
	t.Log(tree.calc(1, 3))
	t.Log(tree.smtNode2)
}
