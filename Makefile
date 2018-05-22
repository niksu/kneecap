.PHONY: clean all

all:
	make -C kneecap
	make -C kneet

clean:
	make -C kneecap clean
	make -C kneet clean
