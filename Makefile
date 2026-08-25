COQPROJECT := _CoqProject
ROCQMAKEFILE := Makefile.rocq
VFILES := $(shell find . -name '*.v')

.PHONY: all clean

all: $(ROCQMAKEFILE)
	$(MAKE) -f $(ROCQMAKEFILE)

$(ROCQMAKEFILE): $(COQPROJECT) $(VFILES)
	rocq makefile -f $(COQPROJECT) -o $(ROCQMAKEFILE)

clean:
	@if [ -f $(ROCQMAKEFILE) ]; then \
		$(MAKE) -f $(ROCQMAKEFILE) clean; \
	fi
	rm -f $(ROCQMAKEFILE)
