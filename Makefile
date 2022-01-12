###################################################################################################
#  make			 "for release version"
#  make d		 "debug version"
#  make p		 "profiling version"
#  make clean   	 "remove object files and executable"
###################################################################################################
.PHONY:	r d p lr ld lp all install install-bin clean distclean
all: r

## Configurable options ###########################################################################

## Cplex library location (configure these variables)
LINUX_CPLEXLIBDIR   ?= /w/63/fbacchus/CPLEX_Studio1210/cplex/lib/x86-64_linux/static_pic
LINUX_CPLEXINCDIR   ?= /w/63/fbacchus/CPLEX_Studio1210/cplex/include

## Cplex libary on mac vm
LINUXVM_CPLEXLIBDIR   ?= /home/fbacchus/CPLEX_Studio1210/cplex/lib/x86-64_linux/static_pic
LINUXVM_CPLEXINCDIR   ?= /home/fbacchus/CPLEX_Studio1210/cplex/include
#
#If you want to build on macos
DARWIN_CPLEXLIBDIR   ?= /Users/fbacchus/Applications/IBM/ILOG/CPLEX_Studio1210/cplex/lib/x86-64_osx/static_pic/
DARWIN_CPLEXINCDIR   ?= /Users/fbacchus/Applications/IBM/ILOG/CPLEX_Studio1210/cplex/include

ifeq "$(shell uname)" "Linux"
CPLEXLIBDIR   =$(LINUX_CPLEXLIBDIR)
CPLEXINCDIR   =$(LINUX_CPLEXINCDIR)
endif
ifeq "$(shell uname)" "Darwin"
CPLEXLIBDIR   =$(DARWIN_CPLEXLIBDIR)
CPLEXINCDIR   =$(DARWIN_CPLEXINCDIR)
endif
ifeq "$(shell hostname)" "ubuntu-vm"
CPLEXLIBDIR   =$(LINUXVM_CPLEXLIBDIR)
CPLEXINCDIR   =$(LINUXVM_CPLEXINCDIR)
endif

# Directory to store object files, libraries, executables, and dependencies:
BUILD_DIR      ?= build

# Include debug-symbols in release builds?
#MAXHS_RELSYM ?= -g

MAXHS_REL    ?= -O3 -DNDEBUG -DNCONTRACTS -DNTRACING
#MAXHS_REL    += -DLOGGING
#MAXHS_REL   += -DQUITE
#MAXHS_DEB    ?= -O0 -DDEBUG -D_GLIBCXX_DEBUG -ggdb
MAXHS_DEB    ?= -O0 -DDEBUG -ggdb
MAXHS_PRF    ?= -O3 -DNDEBUG


ifneq "$(CXX)" "clang++"
MAXHS_REL    += -flto 
endif
# Target file names
MAXHS      = maxhs#       Name of Maxhs main executable.
MAXHS_SLIB = lib$(MAXHS).a#  Name of Maxhs static library.

#-DIL_STD is a IBM/CPLEX issue

MAXHS_CXXFLAGS = -DIL_STD -I. -I$(CPLEXINCDIR)
MAXHS_CXXFLAGS += -Wall -Wno-parentheses -Wextra -Wno-deprecated
MAXHS_CXXFLAGS += -std=c++14

MAXHS_LDFLAGS  = -Wall -lz -L$(CPLEXLIBDIR) -lcplex -lpthread -ldl -flto

ECHO=@echo

ifeq ($(VERB),)
VERB=@
else
VERB=
endif

MAXHS_SRCS = $(wildcard maxhs/core/*.cc) $(wildcard maxhs/ifaces/*.cc) $(wildcard maxhs/utils/*.cc) \
             $(wildcard minisat/utils/*.cc)
SATSOLVER_SRCS = $(wildcard cadical/src/*.cpp)

OBJS = $(filter-out %Main.o, $(MAXHS_SRCS:.cc=.o))
ALLOBJS = $(MAXHS_SRCS:.cc=.o)
OBJS += $(filter-out %cadical.o %mobical.o, $(SATSOLVER_SRCS:.cpp=.o))
ALLOBJS += $(SATSOLVER_SRCS:.cpp=.o)

r:	$(BUILD_DIR)/release/bin/$(MAXHS)
d:	$(BUILD_DIR)/debug/bin/$(MAXHS)
p:	$(BUILD_DIR)/profile/bin/$(MAXHS)

lr:	$(BUILD_DIR)/release/lib/$(MAXHS_SLIB)
ld:	$(BUILD_DIR)/debug/lib/$(MAXHS_SLIB)
lp:	$(BUILD_DIR)/profile/lib/$(MAXHS_SLIB)

## Build-type Compile-flags:
$(BUILD_DIR)/release/%.o:           MAXHS_CXXFLAGS +=$(MAXHS_REL) $(MAXHS_RELSYM)
$(BUILD_DIR)/debug/%.o:				MAXHS_CXXFLAGS +=$(MAXHS_DEB)
$(BUILD_DIR)/profile/%.o:			MAXHS_CXXFLAGS +=$(MAXHS_PRF) -pg

## Build-type Link-flags:
$(BUILD_DIR)/profile/bin/$(MAXHS):		MAXHS_LDFLAGS += -pg
ifeq "$(shell uname)" "Linux"
$(BUILD_DIR)/release/bin/$(MAXHS):		MAXHS_LDFLAGS += --static -z muldefs
endif
$(BUILD_DIR)/release/bin/$(MAXHS):		MAXHS_LDFLAGS += $(MAXHS_RELSYM)

## Executable dependencies
$(BUILD_DIR)/release/bin/$(MAXHS):	 	$(BUILD_DIR)/release/maxhs/core/Main.o $(foreach o,$(OBJS),$(BUILD_DIR)/release/$(o))
$(BUILD_DIR)/debug/bin/$(MAXHS):	 	$(BUILD_DIR)/debug/maxhs/core/Main.o $(foreach o,$(OBJS),$(BUILD_DIR)/debug/$(o))
#$(BUILD_DIR)/debug/bin/$(MAXHS):	 	$(BUILD_DIR)/debug/maxhs/core/Main.o $(BUILD_DIR)/debug/lib/$(MAXHS_SLIB)
#$(BUILD_DIR)/profile/bin/$(MAXHS):	 	$(BUILD_DIR)/profile/maxhs/core/Main.o $(BUILD_DIR)/profile/lib/$(MAXHS_SLIB)

## Library dependencies
#$(BUILD_DIR)/release/lib/$(MAXHS_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/release/$(o))
#$(BUILD_DIR)/debug/lib/$(MAXHS_SLIB):		$(foreach o,$(OBJS),$(BUILD_DIR)/debug/$(o))
#$(BUILD_DIR)/profile/lib/$(MAXHS_SLIB):	$(foreach o,$(OBJS),$(BUILD_DIR)/profile/$(o))

## Compile rules 
$(BUILD_DIR)/release/%.o:	%.cc
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/release/$*.d
$(BUILD_DIR)/release/%.o:	%.cpp
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/release/$*.d

$(BUILD_DIR)/profile/%.o:	%.cc
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/profile/$*.d
$(BUILD_DIR)/profile/%.o:	%.cpp
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/release/$*.d

$(BUILD_DIR)/debug/%.o:	%.cc
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/debug/$*.d
$(BUILD_DIR)/debug/%.o:	%.cpp
	$(ECHO) Compiling: $@
	$(VERB) mkdir -p $(dir $@)
	$(VERB) $(CXX) $(MAXHS_CXXFLAGS) $(CXXFLAGS) -c -o $@ $< -MMD -MF $(BUILD_DIR)/release/$*.d

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

clean:
	rm -f $(foreach t, release debug profile, $(foreach o, $(ALLOBJS), $(BUILD_DIR)/$t/$o)) \
      $(foreach t, release debug profile, $(foreach d, $(ALLOBJS:.o=.d), $(BUILD_DIR)/$t/$d)) \
	  $(foreach t, release debug profile, $(BUILD_DIR)/$t/bin/$(MAXHS))\


## Include generated dependencies
DEPS = $(foreach b, release, $(foreach d, $(ALLOBJS:.o=.d), $(BUILD_DIR)/$b/$d))

-include $(DEPS)
