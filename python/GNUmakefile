SRCS=left_pad.py

.PHONY: all
all: types lint test

.PHONY: types
types: $(SRCS)
	mypy $^

.PHONY: lint
lint: $(SRCS)
	python3 -m deal lint $^

.PHONY: test
test: $(SRCS)
	python3 -m deal test $^
