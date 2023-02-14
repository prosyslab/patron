MAKE=@make
DUNE=@dune
LN=@ln -sf
RM=@rm
EXE=patron
TRANSFORMER=transformer

all:
	$(DUNE) build src/main.exe
	$(LN) _build/default/src/main.exe $(EXE)
	$(DUNE) build src/transformer.exe
	$(LN) _build/default/src/transformer.exe $(TRANSFORMER)

test: all
	$(MAKE) -C test
	$(DUNE) test

clean:
	$(DUNE) clean
	$(RM) -rf $(EXE)
