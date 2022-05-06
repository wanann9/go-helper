package contest

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
