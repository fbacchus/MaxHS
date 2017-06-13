###################################################################################################
#  make			 "for a satically linked release version"
#  make d		 "debug version"
#  make p		 "profiling version"
#  make config  	 "Set up local locations, see README"
#  make install 	 "install maxhs executable"
#  make clean   	 "remove object files and executable"
#  make distclean 	 "clean and undo config"
###################################################################################################
.PHONY:	r d p lr ld lp  config all install install-bin clean distclean
all: r lr 

## Load Previous Configuration ####################################################################

-include config.mk

## Configurable options ###########################################################################

## Cplex library location (configure these variables with "make config")
LINUX_CPLEXLIBDIR   ?= /w/63/fbacchus/CPLEX_Studio127/cplex/lib/x86-64_linux/static_pic
LINUX_CPLEXINCDIR   ?= /w/63/fbacchus/CPLEX_Studio127/cplex/include
##
DARWIN_CPLEXLIBDIR   ?= /Users/fbacchus/Applications/IBM/ILOG/CPLEX_Studio127/cplex/lib/x86-64_osx/static_pic/
DARWIN_CPLEXINCDIR   ?= /Users/fbacchus/Applications/IBM/ILOG/CPLEX_Studio127/cplex/include

ifeq "$(shell uname)" "Linux"
CPLEXLIBDIR   =$(LINUX_CPLEXLIBDIR)
CPLEXINCDIR   =$(LINUX_CPLEXINCDIR)
endif
ifeq "$(shell uname)" "Darwin"
CPLEXLIBDIR   =$(DARWIN_CPLEXLIBDIR)
CPLEXINCDIR   =$(DARWIN_CPLEXINCDIR)
endif

# Directory to store object files, libraries, executables, and dependencies:
BUILD_DIR      ?= build

# Include debug-symbols in release builds?
MAXHS_RELSYM ?= -g

# Sets of compile flags for different build types
MAXHS_REL    ?= -O3 -D NDEBUG
MAXHS_DEB    ?= -O0 -D DEBUG -D_GLIBCXX_DEBUG -ggdb
MAXHS_PRF    ?= -O3 -D NDEBUG

# GNU Standard Install Prefix
prefix         ?= /usr/local

## Write Configuration  ###########################################################################

config:
	@( echo 'BUILD_DIR?=$(BUILD_DIR)'       ; \
	   echo 'MAXHS_RELSYM?=$(MAXHS_RELSYM)' ; \
	   echo 'MAXHS_REL?=$(MAXHS_REL)'       ; \
	   echo 'MAXHS_DEB?=$(MAXHS_DEB)'       ; \
	   echo 'MAXHS_PRF?=$(MAXHS_PRF)'       ; \
	   echo LINUX_CPLEXLIBDIR?=$(LINUX_CPLEXLIBDIR) ; \
	   echo LINUX_CPLEXINCDIR?=$(LINUX_CPLEXINCDIR) ; \
	   echo DARWIN_CPLEXLIBDIR?=$(DARWIN_CPLEXLIBDIR) ; \
	   echo DARWIN_CPLEXINCDIR?=$(DARWIN_CPLEXINCDIR) ; \
	   echo 'prefix?=$(prefix)'                 ) > config.mk

## Configurable options end #######################################################################

INSTALL ?= install

# GNU Standard Install Variables
exec_prefix ?= $(prefix)
includedir  ?= $(prefix)/include
bindir      ?= $(exec_prefix)/bin
libdir      ?= $(exec_prefix)/lib
datarootdir ?= $(prefix)/share
mandir      ?= $(datarootdir)/man

# Target file names
MAXHS      = maxhs#       Name of Maxhs main executable.
MAXHS_SLIB = lib$(MAXHS).a#  Name of Maxhs static library.

#-DIL_STD is a IBM/CPLEX issue

MAXHS_CXXFLAGS = -DIL_STD -I. -I$(CPLEXINCDIR)
MAXHS_CXXFLAGS += -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS 
MAXHS_CXXFLAGS += -Wall -Wno-parentheses -Wextra -Wno-deprecated
MAXHS_CXXFLAGS += -std=c++11

MAXHS_LDFLAGS  = -Wall -lz -L$(CPLEXLIBDIR) -lcplex -lpthread

ECHO=@echo

ifeq ($(VERB),)
VERB=@
else
VERB=
endif

SRCS = $(wildcard minisat/core/*.cc) $(wildcard minisat/simp/*.cc) $(wildcard minisat/utils/*.cc) \
       $(wildcard maxhs/core/*.cc) $(wildcard maxhs/ifaces/*.cc) \
       $(wildcard maxhs/utils/*.cc) 
MINISAT_HDRS = $(wildcard minisat/mtl/*.h) $(wildcard minisat/core/*.h) \
       $(wildcard minisat/utils/*.h) $(wildcard minisat/simp/*.h) 
MAXHS_HDRS = $(wildcard maxhs/core/*.h) $(wildcard maxhs/ifaces/*.h) \
       $(wildcard maxhs/ds/*.h) $(wildcard maxhs/utils/*.h) 

OBJS = $(filter-out %Main.o, $(SRCS:.cc=.o))

r:	$(BUILD_DIR)/release/bin/$(MAXHS)
d:	$(BUILD_DIR)/debug/bin/$(MAXHS)
p:	$(BUILD_DIR)/profile/bin/$(MAXHS)

lr:	$(BUILD_DIR)/release/lib/$(MAXHS_SLIB)
ld:	$(BUILD_DIR)/debug/lib/$(MAXHS_SLIB)
lp:	$(BUILD_DIR)/profile/lib/$(MAXHS_SLIB)


## Build-type Compile-flags:
$(BUILD_DIR)/release/%.o:			MAXHS_CXXFLAGS +=$(MAXHS_REL) $(MAXHS_RELSYM)
$(BUILD_DIR)/debug/%.o:				MAXHS_CXXFLAGS +=$(MAXHS_DEB) -ggdb
$(BUILD_DIR)/profile/%.o:			MAXHS_CXXFLAGS +=$(MAXHS_PRF) -pg

## Build-type Link-flags:
$(BUILD_DIR)/profile/bin/$(MAXHS):		MAXHS_LDFLAGS += -pg
ifeq "$(shell uname)" "Linux"
$(BUILD_DIR)/release/bin/$(MAXHS):		MAXHS_LDFLAGS += --static -z muldefs
endif
$(BUILD_DIR)/release/bin/$(MAXHS):		MAXHS_LDFLAGS += $(MAXHS_RELSYM)

## Executable dependencies
$(BUILD_DIR)/release/bin/$(MAXHS):	 	$(BUILD_DIR)/release/maxhs/core/Main.o $(BUILD_DIR)/release/lib/$(MAXHS_SLIB)
$(BUILD_DIR)/debug/bin/$(MAXHS):	 	$(BUILD_DIR)/debug/maxhs/core/Main.o $(BUILD_DIR)/debug/lib/$(MAXHS_SLIB)
$(BUILD_DIR)/profile/bin/$(MAXHS):	 	$(BUILD_DIR)/profile/maxhs/core/Main.o $(BUILD_DIR)/profile/lib/$(MAXHS_SLIB)

## Library dependencies
$(BUILD_DIR)/release/lib/$(MAXHS_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/release/$(o))
$(BUILD_DIR)/debug/lib/$(MAXHS_SLIB):		$(foreach o,$(OBJS),$(BUILD_DIR)/debug/$(o))
$(BUILD_DIR)/profile/lib/$(MAXHS_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/profile/$(o))

## Compile rules 
$(BUILD_DIR)/release/%.o:	%.cc
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/release/$*.d

$(BUILD_DIR)/profile/%.o:	%.cc
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/profile/$*.d

$(BUILD_DIR)/debug/%.o:	%.cc
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/debug/$*.d

## Linking rule
$(BUILD_DIR)/release/bin/$(MAXHS) $(BUILD_DIR)/debug/bin/$(MAXHS) $(BUILD_DIR)/profile/bin/$(MAXHS):
	$(ECHO) Linking Binary: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $^ $(MAXHS_LDFLAGS) $(LDFLAGS) -o $@

## Static Library rule
%/lib/$(MAXHS_SLIB):
	$(ECHO) Linking Static Library: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(AR) -rcs $@ $^

install:	install-headers install-lib install-bin

install-debug:	install-headers install-lib-debug

install-headers:
#       Create directories
	$(INSTALL) -d $(DESTDIR)$(includedir)/maxhs
	$(INSTALL) -d $(DESTDIR)$(includedir)/minisat
#
	for dir in maxhs/core maxhs/ifaces maxhs/ds maxhs/utils; do \
	  $(INSTALL) -d $(DESTDIR)$(includedir)/$$dir ; \
        done
	for dir in minisat/mtl minisat/utils minisat/core minisat/simp; do \
	  $(INSTALL) -d $(DESTDIR)$(includedir)/$$dir ; \
	done
# Install headers
	for h in $(MINISAT_HDRS) ; do \
	  $(INSTALL) -m 644 $$h $(DESTDIR)$(includedir)/$$h ; \
	done
	for h in $(MAXHS_HDRS) ; do \
	  $(INSTALL) -m 644 $$h $(DESTDIR)$(includedir)/$$h ; \
	done


install-lib-debug: $(BUILD_DIR)/debug/lib/$(MAXHS_SLIB)
	$(INSTALL) -d $(DESTDIR)$(libdir)
	$(INSTALL) -m 644 $(BUILD_DIR)/debug/lib/$(MAXHS_SLIB) $(DESTDIR)$(libdir)

install-lib: $(BUILD_DIR)/release/lib/$(MAXHS_SLIB) 
	$(INSTALL) -d $(DESTDIR)$(libdir)
	$(INSTALL) -m 644 $(BUILD_DIR)/release/lib/$(MAXHS_SLIB) $(DESTDIR)$(libdir)

install-bin: $(BUILD_DIR)/release/bin/$(MAXHS)
	$(INSTALL) -d $(DESTDIR)$(bindir)
	$(INSTALL) -m 755 $(BUILD_DIR)/release/bin/$(MAXHS) $(DESTDIR)$(bindir)

clean:
	rm -f $(foreach t, release debug profile, $(foreach o, $(SRCS:.cc=.o), $(BUILD_DIR)/$t/$o)) \
          $(foreach t, release debug profile, $(foreach d, $(SRCS:.cc=.d), $(BUILD_DIR)/$t/$d)) \
	  $(foreach t, release debug profile, $(BUILD_DIR)/$t/bin/$(MAXHS)) \
	  $(foreach t, release debug profile, $(BUILD_DIR)/$t/lib/$(MAXHS_SLIB))

distclean:	clean
	rm -f config.mk

## Include generated dependencies
-include $(foreach s, $(SRCS:.cc=.d), $(BUILD_DIR)/release/$s)
-include $(foreach s, $(SRCS:.cc=.d), $(BUILD_DIR)/debug/$s)
-include $(foreach s, $(SRCS:.cc=.d), $(BUILD_DIR)/profile/$s)
