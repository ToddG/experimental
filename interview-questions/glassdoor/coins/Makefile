.PHONY: all
all:
	mypy python/coins.py --ignore-missing-imports
	pytest python/coins.py --hypothesis-show-statistics
	python3 python/coins.py
