MAKE=@make
DUNE=@dune
LN=@ln -sf
RM=@rm
EXE=patron

all:
	-$(DUNE) build @fmt --auto-promote src/main.exe
	$(LN) _build/default/src/main.exe $(EXE)

test: all
	$(MAKE) -C test
	$(DUNE) test

promote:
	$(DUNE) promote

clean:
	$(DUNE) clean
	$(RM) -rf $(EXE)
