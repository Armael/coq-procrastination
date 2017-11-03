##############################################################################
# Certain custom settings can be defined in settings.sh.

# To specify the location of the Coq binaries, define COQBIN (with a
# trailing slash), e.g. COQBIN=/var/tmp/coq/bin/.
# If COQBIN is undefined, then "coqc" is used.

# To request creation of .vio files, as opposed to creation of .vo
# files, define SERIOUS=0.

SERIOUS := 1

CONTRIB := $(shell $(COQBIN)coqc -where)/user-contrib

############################################################################
# Compilation.

export COQINCLUDE := \
  -R $(shell pwd) Procrastinate \

export SERIOUS

.PHONY: all clean

all:
	$(MAKE) -f Makefile.coq _CoqProject
	$(MAKE) -f Makefile.coq $@

clean:
	$(MAKE) -f Makefile.coq $@

############################################################################
# Installation.

TARGET  := $(CONTRIB)/Procrastinate

.PHONY: install uninstall

install:
	rm -rf $(TARGET)
	mkdir -p $(TARGET)
	install -m 644 *.v *.vo *.glob Makefile Makefile.coq $(TARGET)
ifeq ($(SERIOUS),0)
	install -m 644 *.vio $(TARGET)
endif

uninstall:
	rm -rf $(TARGET)
