# Delegate these commands.

.PHONY: all clean install uninstall

all install uninstall:
	@ $(MAKE) -C src $@

examples: all
	@ $(MAKE) -C examples

clean:
	@ $(MAKE) -C src $@
	@ $(MAKE) -C examples $@
