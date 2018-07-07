# Delegate these commands.

.PHONY: all clean examples manual install

all:
	@ $(MAKE) -C src $@

examples: all
	@ $(MAKE) -C examples

manual:
	@ $(MAKE) -C manual

install:
	@ $(MAKE) -C src $@

clean:
	@ $(MAKE) -C src $@
	@ $(MAKE) -C examples $@
	@ $(MAKE) -C manual $@
