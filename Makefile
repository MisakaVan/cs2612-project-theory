CURRENT_DIR=.
SETS_DIR = sets
COMPCERT_DIR = compcert_lib
LISTOP_DIR = ListOperation
# PL_DIR = pl
ASSIGNMENT_DIR = Assignment

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

# PL_FLAG = -R $(PL_DIR) PL -R $(SETS_DIR) SetsClass -R $(COMPCERT_DIR) compcert.lib -R $(ASSIGNMENT_DIR) PL.Assignment

SETS_FLAG = -R $(SETS_DIR) SetsClass

COMPCERT_FLAG = -R $(COMPCERT_DIR) compcert.lib

LISTOP_FLAG = -R $(LISTOP_DIR) ListOperation

DEP_FLAG = $(SETS_FLAG) $(COMPCERT_FLAG) $(LISTOP_FLAG)


SETS_FILE_NAMES = \
   SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v
SETS_FILES=$(SETS_FILE_NAMES:%.v=$(SETS_DIR)/%.v)

COMPCERT_FILE_NAMES = \
    Coqlib.v Integers.v Zbits.v
COMPCERT_FILES=$(COMPCERT_FILE_NAMES:%.v=$(COMPCERT_DIR)/%.v)

LISTOP_FILE_NAMES = \
	ListOperation.v
LISTOP_FILES=$(LISTOP_FILE_NAMES:%.v=$(LISTOP_DIR)/%.v)



FILES = $(SETS_FILES) \
  $(COMPCERT_FILES) \
  $(LISTOP_FILES) \

$(SETS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<;
	@$(COQC) $(SETS_FLAG) $<

$(COMPCERT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<;
	@$(COQC) $(COMPCERT_FLAG) $<

$(LISTOP_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<;
	@$(COQC) $(LISTOP_FLAG) $<

all: $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob;
	@rm -f *.vo */*.vo;
	@rm -f *.vok */*.vok;
	@rm -f *.vos */*.vos; 
	@rm -f .*.aux */.*.aux;
	@rm -f .depend;

.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend
