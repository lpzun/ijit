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
FLEXSUFF	= ll
FLEXCOMP	= flex 
FLEXOBJ 	= $(BASE).$(FLEXSUFF)
FEXPORT		= lex.yy.c

#bison
BISONSUFF	= yy
BISONCOMP 	= bison
BISONOBJ 	= $(BASE).$(BISONSUFF)
BISONFLAG 	= -d
#the export of flex and bison
BEXPORT		= $(BASE).tab.cc $(BASE).tab.hh location.hh position.hh stack.hh

CBASE 		= $(BASE)
CCOMP 		= g++ #the name of the compiler
CCOBJS 		= $(BASE).tab.cc $(BASE).cc
DEBUG 		= -g
CFLAGS 		= -Wall -c $(DEBUG)
LFLAGS 		= -Wall $(DEBUG)
CEXPORT 	= *.h *.cfg *.loc *.taf

#========================================
# main cmds		#
# $(CCOMP) $(LFLAGS) $(CCOBJS) -o $(CBASE) -lfl #does not work on Mac if append -lfl
#========================================

all:
	$(FLEXCOMP) $(FLEXOBJ) 
	$(BISONCOMP) $(BISONFLAG) $(BISONOBJ)
	$(call rename)
	#$(CCOMP) $(LFLAGS) $(CCOBJS) -o $(CBASE)

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
