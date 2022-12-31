package main

import "testing"

func Test_trie(t *testing.T) {
	trie := tr(numbers + letters)
	t.Log(trie)
	t.Log(trie.insert("a", 1))
	t.Log(trie.insert("ab", 2))
	t.Log(trie.search(""))
	t.Log(trie.search("a"))
	t.Log(trie.delete("a", 2))
	t.Log(trie.delete("a", -1))
	t.Log(trie.search("ab"))
	t.Log(trie.delete("ab", 1))
}

func Test_trie01(t *testing.T) {
	trie := tr01(2)
	trie.insert(0, 1)
	trie.insert(1, 1)
	trie.insert(2, 1)
	trie.insert(3, 1)
	t.Log(trie.query(0))
	t.Log(trie.query(1))
	t.Log(trie.query(2))
	t.Log(trie.query(3))
}
