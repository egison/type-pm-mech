JOBNAME = type-pm-mech
SOURCE = main

.PHONY: all clean cleanAll

all: $(SOURCE).tex
	lualatex -interaction=nonstopmode -halt-on-error -jobname=$(JOBNAME) $(SOURCE)
	lualatex -interaction=nonstopmode -halt-on-error -jobname=$(JOBNAME) $(SOURCE)

clean:
	rm -f $(JOBNAME).aux $(JOBNAME).log $(JOBNAME).out $(JOBNAME).toc

cleanAll: clean
	rm -f $(JOBNAME).pdf
