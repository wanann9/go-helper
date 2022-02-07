package pkg

import (
	"fmt"
	"runtime/debug"
)

type Error interface {
	error

	Stack() string
}

func NewError(format string, args ...interface{}) Error {
	return newErrorWithStack(fmt.Sprintf(format, args...), "")
}

func NewErrorWithStack(format string, args ...interface{}) Error {
	return newErrorWithStack(fmt.Sprintf(format, args...), string(debug.Stack()))
}

type errorWithStack struct {
	err   string
	stack string
}

func newErrorWithStack(err, stack string) *errorWithStack {
	return &errorWithStack{
		err:   err,
		stack: stack,
	}
}

func (e *errorWithStack) Error() string {
	return e.err
}

func (e *errorWithStack) Stack() string {
	return e.stack
}

type ErrorFormatter struct {
	format string
}

func NewErrorFormatter(format string, args ...interface{}) *ErrorFormatter {
	if len(args) > 0 {
		format = fmt.Sprintf(format, args...)
	}

	return &ErrorFormatter{
		format: format,
	}
}

func (f *ErrorFormatter) WithArgs(args ...interface{}) Error {
	return newErrorWithStack(fmt.Sprintf(f.format, args...), "")
}

func (f *ErrorFormatter) WithArgsAndStack(args ...interface{}) Error {
	return newErrorWithStack(fmt.Sprintf(f.format, args...), string(debug.Stack()))
}

func (f *ErrorFormatter) String() string {
	return f.format
}
