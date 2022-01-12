CADICALBUILD=/Users/fbacchus/MaxSat/cadical/build
all:
	$(MAKE) -C "$(CADICALBUILD)"
clean:
	@if [ -d "$(CADICALBUILD)" ]; \
	then \
	  if [ -f "$(CADICALBUILD)"/makefile ]; \
	  then \
	     touch "$(CADICALBUILD)"/build.hpp; \
	     $(MAKE) -C "$(CADICALBUILD)" clean; \
	  fi; \
	  rm -rf "$(CADICALBUILD)"; \
	fi
	rm -f "/Users/fbacchus/MaxSat/cadical/makefile"
test:
	$(MAKE) -j1 -C "$(CADICALBUILD)" test
cadical:
	$(MAKE) -j1 -C "$(CADICALBUILD)" cadical
mobical:
	$(MAKE) -j1 -C "$(CADICALBUILD)" mobical
update:
	$(MAKE) -j1 -C "$(CADICALBUILD)" update
.PHONY: all cadical clean mobical test update
