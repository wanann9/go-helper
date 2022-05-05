package contest

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
