PKG=.

test:
	go test -race -cover -count=1 "$(PKG)/..."

test-v:
	go test -v -race -cover -count=1 "$(PKG)/..."
