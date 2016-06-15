# Generic C++ Makefile

###########################################################################
# 1. Public Region. The following settings are useful for compiling a     #
# single executable file out of many source files (*.c). If the directory #
# contains many independent files to be compiled to independent           #
# executables, use SOURCES=$(BASE).c, HEADERS=$(BASE).h.                  #
###########################################################################
# Override these variables (or add new ones) locally
API	         = libijit # the name of application
OUTPUTFILE   = $(API).dylib #libijit.dylib.1.0

LIBDIR       = lib
INCLUDEDIR   = include

INSTALLDIR   = /usr/local/ijit# config your install directory

# Setup compiler flags and includes
SATDIR       =# /usr/local/                  
ILIBS        =# -L $(SATDIR)/yourlib -lyourlib       # config your lib                            
IINCLUDE     =# -I $(SATDIR)/include/                # config your includes                                     
ISTD	     = -std=c++11                            # using c++11 or above

# Setup compiling source
CSUFF        = cc
# CSUFF       = cpp
SRCDIR       = src 
SRCDIRS      = $(shell find $(SRCDIR) -name '*.$(CSUFF)' -exec dirname {} \; | uniq)

BASE         = $(LIBDIR)/$(API)
DEFAULT      = $(BASE)
FLAGS        = -Wall -g $(ISTD)#           -O3, -D__SAFE_COMPUTATION__, etc
SOURCES      = $(shell find $(SRCDIR) -name '*.$(CSUFF)') 
              #$(wildcard *.$(CSUFF))#  list of local files that will be compiled
                                     #   and linked into executable

# For compiling:
IDIRS        =#                                   -I$(C)
HEADERS      = $(wildcard *.$(HSUFF))#  may set to a single .h file if only one 
                                     #  specific file is compiled

# For linking:
BASE         = $(LIBDIR)/$(OUTPUTFILE)
ROBJVARS     =
LDIRS        =#
LIBS         =$(ILIBS)#                                   -lm

EXPORT       = CCOMP=$(CCOMP) FLAGS="$(FLAGS)"

DISTCLEAN    =# any additional commands to be executed by the distclean command 
              # (like cleaning sub directories)
              
INSTALL     = $(call installation)#

#####################################
# 2. Private Region (do not change) #
#####################################

ifeq ($(CSUFF),cc)
  HSUFF        = hh
  TSUFF        = CC
  CCOMP        = g++
else
  HSUFF        = h
  TSUFF        = C
  CCOMP        = gcc
endif

OS            := $(shell sh -c 'uname -s 2>/dev/null || echo not')
ifeq ($(OS), Darwin)
  LIBSUFF      = dylib
endif
ifeq ($(OS), Linux)
  LIBSUFF      = so
endif
ifeq ($(OS), Cygwin)
  LIBSUFF      = dll
endif

AR             = ar
ARFLAGS        = rcs
VERSION        = 1.0

STATIC         = static
SHARED         = shared

SHELL          = /bin/bash
BASES          = $(wildcard *.$(CSUFF))
BASES         := $(BASES:.$(CSUFF)=)
LOBJECTS       = $(patsubst %.$(CSUFF),$(OBJDIR)/%.o, $(SOURCES:.$(CSUFF)=.o))# 
RDIRS          = $(foreach VAR,$(ROBJVARS),$(dir $(firstword $($(VAR)))))
ROBJECTS       = $(foreach VAR,$(ROBJVARS),$($(VAR)))
OBJECTS        = $(LOBJECTS) $(ROBJECTS)
CFLAGS         = $(FLAGS) $(IDIRS) $(IINCLUDE)#
LFLAGS         = $(FLAGS) $(LDIRS)
RERROR         = { echo "error in recursive make robjects";  exit 1; }
DERROR         = { echo "error in recursive make distclean"; exit 1; }

default: $(DEFAULT)

edit:
	editor $(EDITFILES) &

new: clean default

distnew: distclean default

# Add new targets locally. This is included after 'default' above, so that 
# the default remains the default.
-include makefile-local-targets

# do not export variables by default (only those mentioned in EXPORT)
unexport MAKEFLAGS

##################################
# Targets Region (do not change) #
##################################

$(DEFAULT): $(OBJECTS)
	@mkdir -p `dirname $@`
	$(AR) $(ARFLAGS) $@ $^
	ranlib $@

$(OBJECTS): %.o: %.$(CSUFF) $(HEADERS)
	$(CCOMP) $(CFLAGS) $< -c -o $@
	
install: INSTALLOBJS
    
robjects:
	$(foreach VAR,$(ROBJVARS),$(MAKE) -C $(dir $(firstword#
		$($(VAR)))) $(EXPORT) $(notdir $($(VAR))) || $(RERROR);)
	
INSTALLOBJS: 
	@$(call installation)
	
define installation
    mkdir -p $(INSTALLDIR)/lib/
    mkdir -p $(INSTALLDIR)/include/
    cp -rf lib/$(OUTPUTFILE) $(INSTALLDIR)/lib/
    #ln -sf $(INSTALLDIR)/lib/$(OUTPUTFILE) $(INSTALLDIR)/lib/libijit.dylib
endef
		
##################################
# Cleaning (do not change)       #
##################################

clean: 	CLEANOBJS
	rm -f *.o a.out

distclean: clean CLEANOBJS
	rm -rf $(LIBDIR)
	rm -f *~
	$(foreach DIR,$(RDIRS),$(MAKE) -C $(DIR) $(EXPORT) distclean || $(DERROR);)
	$(DISTCLEAN)

CLEANOBJS:
	@$(call clean-obj)

# description: for cleaning all objects
define clean-obj
	find . -name '*.o' -type f -delete
endef


