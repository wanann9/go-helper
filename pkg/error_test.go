package pkg

import "testing"

func TestError(t *testing.T) {
	err := NewError("%v", "error")
	t.Log(err)
	t.Log(err.Stack())

	err = NewErrorWithStack("%v", "error")
	t.Log(err)
	t.Log(err.Stack())
}

func TestErrorFormatter(t *testing.T) {
	err := NewErrorFormatter("%v")
	t.Log(err)
	t.Log(err.WithArgs("error"))
	t.Log(err.WithArgsAndStack("error").Stack())

	err = NewErrorFormatter("%%v%v", "")
	t.Log(err)
	t.Log(err.WithArgsAndStack("error"))
	t.Log(err.WithArgs("error").Stack())
}
