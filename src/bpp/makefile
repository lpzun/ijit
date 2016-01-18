####################################################################################
# This is the makefile for boolean program parser: BoPP
# 	
# @author: 	Peizun Liu
# @Copyright: 	It belongs to Thomas Wahl's group in CAR Lab, CCIS, NEU
####################################################################################

#========================================
# macro definition		#
#========================================

BASE 		= bopp_bw
#DIR
#EXPDIR

#flex
FLEXSUFF	= lex
FLEXCOMP	= flex 
FLEXOBJ 	= $(BASE).$(FLEXSUFF)
FEXPORT		= lex.yy.c

#bison
BISONSUFF	= y
BISONCOMP 	= bison
BISONOBJ 	= $(BASE).$(BISONSUFF)
BISONFLAG 	= -d
#the export of flex and bison
BEXPORT		= $(BASE).tab.cc $(BASE).tab.hh location.hh position.hh stack.hh
SUPPORT     = bopp.cc bopp.hh

CBASE 		= $(BASE)
CCOMP 		= g++ #the name of the compiler
CCOBJS 		= $(BASE).tab.cc $(FEXPORT) bopp.cc
ISTD	    = -std=c++11
DEBUG 		= -g
CFLAGS 		= -Wall -c $(DEBUG) $(ISTD)#
LFLAGS 		= -Wall $(DEBUG) $(ISTD)#
CEXPORT 	= *.h *.cfg *.loc *.taf

#========================================
# main cmds		#
# $(CCOMP) $(LFLAGS) $(CCOBJS) -o $(CBASE) -lfl #does not work on Mac if append -lfl
#========================================

all:
	$(FLEXCOMP) $(FLEXOBJ) 
	$(BISONCOMP) $(BISONFLAG) $(BISONOBJ)
	#$(call rename)
	$(CCOMP) $(LFLAGS) $(CCOBJS) -o $(CBASE)

#========================================
# Cleaning 		#
#========================================
clean:
	rm -f $(FEXPORT) $(BEXPORT) $(BASE).cc

distclean: clean
	rm -f $(CBASE) $(CEXPORT) *~

RENAME:
	@$(call rename)
# rename the lex.yy.c file
define rename
	mv $(FEXPORT) $(BASE).cc
endef
