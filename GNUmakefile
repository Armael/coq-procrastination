# Delegate these commands.

.PHONY: all clean examples manual

all:
	@ $(MAKE) -C src $@

examples: all
	@ $(MAKE) -C examples

manual:
	@ $(MAKE) -C manual

clean:
	@ $(MAKE) -C src $@
	@ $(MAKE) -C examples $@
	@ $(MAKE) -C manual $@
