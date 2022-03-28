PKGS=$(shell go list ./... | findstr /v "local")

test:
	go test -race -cover -count=1 $(PKGS)

test-v:
	go test -v -race -cover -count=1 $(PKGS)
