/*
 * tclOptimize.c --
 *
 *	This file contains the bytecode optimizer.
 *
 * Copyright (c) 2013 by Donal Fellows.
 * Copyright (c) 2013 by Miguel Sofer.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 */

#include "tclInt.h"
#include "tclCompile.h"
#include <assert.h>

/*
 * Forward declarations.
 */

static void             CompactCode(CompileEnv *envPtr, int *NEW);

/*
 * Helper macros.
 */

#define AddrLength(address) \
    (tclInstructionTable[*(unsigned char *)(address)].numBytes)
#define InstLength(instruction) \
    (tclInstructionTable[(unsigned char)(instruction)].numBytes)

/*
 * Macros used in the code compactor.
 */

#define GET_INT1_AT_PC(pc)			\
    TclGetInt1AtPtr(envPtr->codeStart + (pc))

#define GET_INT4_AT_PC(pc)				\
    TclGetInt4AtPtr(envPtr->codeStart + (pc))

#define GET_UINT1_AT_PC(pc)				\
    TclGetUInt1AtPtr(envPtr->codeStart + (pc))

#define GET_UINT4_AT_PC(pc)			\
    TclGetUInt4AtPtr(envPtr->codeStart + (pc))

#define SET_INT1_AT_PC(i, pc)			\
    TclStoreInt1AtPtr((i), envPtr->codeStart + (pc))

#define SET_INT4_AT_PC(i, pc)				\
    TclStoreInt4AtPtr((i), envPtr->codeStart + (pc))

#define INST_AT_PC(pc)				\
    (*(envPtr->codeStart + (pc)))

#define NEXT_PC(pc)				\
    pc + InstLength(INST_AT_PC(pc))

/*
 * ----------------------------------------------------------------------
 *
 * CompactCode --
 *
 *	Remove all INST_NOPS and unreachable code. This also shrinks 4-insts
 *	to 1-insts where possible, reduces the code size, and updates all
 *	structs so that the CompileEnv remains consistent.
 *
 * ----------------------------------------------------------------------
 */

static void
CompactCode(
    CompileEnv *envPtr,
    int * NEW)
{
    int pc, nops;
    int inst, i, nextpc;
    int codeSize = (envPtr->codeNext - envPtr->codeStart);

    /*
     * First pass: shrink jumps and push, compute new positions.
     */

    restart:
    pc = 0;
    nops = 0;
    for (pc = 0; pc < codeSize; pc = nextpc) {
	int arg, resize;

	nextpc = NEXT_PC(pc);
	inst = INST_AT_PC(pc);
	NEW[pc] = pc - nops; /* new position */

	resize = 0;
	switch (inst) {
	    case INST_NOP:
		nops++;
		break;

	    case INST_PUSH4:
	    case INST_LOAD_SCALAR4:
	    case INST_LOAD_ARRAY4:
	    case INST_STORE_SCALAR4:
	    case INST_STORE_ARRAY4:
		arg = GET_UINT4_AT_PC(pc+1);
		resize = (arg < 256);
		break;
				
	    case INST_JUMP4:
	    case INST_JUMP_TRUE4:
	    case INST_JUMP_FALSE4:
		arg = GET_INT4_AT_PC(pc+1);
		resize = ((arg < 127) && (arg > -128));
		break;
	}

	if (resize) {
	    /*
	     * INST_XXX1 is always one less than INST_XXX4 
	     */
	    
	    INST_AT_PC(pc) -= 1;
	    SET_INT1_AT_PC(arg, pc+1);
	    INST_AT_PC(pc+2) = INST_NOP;
	    INST_AT_PC(pc+3) = INST_NOP;
	    INST_AT_PC(pc+4) = INST_NOP;
	    nextpc = pc+2; /* get them counted */
	}
    }

    if (nops == 0) {
	return;
    }
    NEW[codeSize] = codeSize - nops;
    
    /*
     * Second pass: move code, update jump offsets, resize the code.
     */
    
    nops = 0;
    for (pc = 0; pc < codeSize; pc = nextpc) {
	int target, i;

	nextpc = NEXT_PC(pc);
	inst = INST_AT_PC(pc);
	if (inst == INST_NOP) {
	    continue;
	}
	
	/* update jump offsets */

	switch (inst) {
	    int offset;
	    ForeachInfo *infoPtr;
	    JumptableInfo *info2Ptr;
	    Tcl_HashEntry *hPtr;
	    Tcl_HashSearch hSearch;

	    case INST_JUMP1:
	    case INST_JUMP_TRUE1:
	    case INST_JUMP_FALSE1:
		target = pc + GET_INT1_AT_PC(pc+1);
		if (offset == 2) {
		    if (inst == INST_JUMP1) {
			INST_AT_PC(pc) = INST_NOP;
			nops++;
		    } else {
			/* warrants a complete optimization restart? */
			INST_AT_PC(pc) = INST_POP;
		    }
		    INST_AT_PC(pc+1) = INST_NOP;
		    nops++;
		} else {
		    SET_INT1_AT_PC(NEW[target]-NEW[pc], pc+1);
		}
		break;

	    case INST_JUMP4:
	    case INST_JUMP_TRUE4:
	    case INST_JUMP_FALSE4:
	    case INST_START_CMD:
		target = pc + GET_INT4_AT_PC(pc+1);
		offset = NEW[target]-NEW[pc];
		SET_INT4_AT_PC(offset, pc+1);
		if (inst != INST_START_CMD) {
		    if (offset == 5) {
			if (inst == INST_JUMP4) {
			    INST_AT_PC(pc) = INST_NOP;
			    nops++;
			} else {
			    /* warrants a complete optimization restart? */
			    INST_AT_PC(pc) = INST_POP;
			}
			INST_AT_PC(pc+1) = INST_NOP;
			INST_AT_PC(pc+2) = INST_NOP;
			INST_AT_PC(pc+3) = INST_NOP;
			INST_AT_PC(pc+4) = INST_NOP;
			nops += 4;
		    } else if ((offset < 127) && (offset > -128)) {
			INST_AT_PC(pc) -= 1;
			SET_INT1_AT_PC(offset, pc+1);
			INST_AT_PC(pc+2) = INST_NOP;
			INST_AT_PC(pc+3) = INST_NOP;
			INST_AT_PC(pc+4) = INST_NOP;
			nops += 3;
		    }
		}
		break;

	    case INST_FOREACH_START:
		i = GET_UINT4_AT_PC(pc+1);
		infoPtr = (ForeachInfo *) TclFetchAuxData(envPtr, i);
		target = pc + 5 - infoPtr->loopCtTemp;
		infoPtr->loopCtTemp = NEW[pc] + 5 - NEW[target];
		break;
		
	    case INST_JUMP_TABLE:
		i = GET_UINT4_AT_PC(pc+1);
		info2Ptr = (JumptableInfo *) TclFetchAuxData(envPtr, i);
		hPtr = Tcl_FirstHashEntry(&info2Ptr->hashTable, &hSearch);
		for (; hPtr ; hPtr = Tcl_NextHashEntry(&hSearch)) {
		    target = pc + PTR2INT(Tcl_GetHashValue(hPtr));
		    Tcl_SetHashValue(hPtr, INT2PTR(NEW[target]-NEW[pc]));
		}
		break;
	}

	/* move up opcode and operands, eliminate  */
	for (i=0; pc+i < nextpc; i++) {
	    INST_AT_PC(NEW[pc]+i) = INST_AT_PC(pc+i);
	}
    }
    envPtr->codeNext = envPtr->codeStart + NEW[codeSize];

    /*
     * Update range targets
     */

    for (i=0 ; i<envPtr->exceptArrayNext ; i++) {
	ExceptionRange *rangePtr = &envPtr->exceptArrayPtr[i];
	int target, after;

	target = rangePtr->codeOffset;
	after  = rangePtr->codeOffset + rangePtr->numCodeBytes;
	rangePtr->codeOffset = NEW[target];
	rangePtr->numCodeBytes = NEW[after] - NEW[target];
	
	if (rangePtr->type == CATCH_EXCEPTION_RANGE) {
	    target = rangePtr->catchOffset;
	    rangePtr->catchOffset = NEW[target];
	} else {
	    target = rangePtr->breakOffset;
	    rangePtr->breakOffset = NEW[target];
	    if (rangePtr->continueOffset >= 0) {
		target = rangePtr->continueOffset;
		rangePtr->continueOffset = NEW[target];
	    }
	}
    }

    /*
     * Update CmdLoc data
     */

    {
	CmdLocation *mapPtr = envPtr->cmdMapPtr;

	for (i=0; i < envPtr->numCommands; i++) {
	    /* After the end of this command's code there is either another
	     * instruction, or else the end of the bytecode. Notice that
	     * numCodeBytes may lie miserably: fix that!
	     */
	    
	    int start = mapPtr[i].codeOffset;
	    int next   = start + mapPtr[i].numCodeBytes;

	    if (next > codeSize) {
		next = codeSize;
	    }
	    mapPtr[i].codeOffset = NEW[start];
	    mapPtr[i].numCodeBytes = NEW[next] - NEW[start];
	}
    }

    /*
     * Restart until all done; should be rare. Other possible criteria:
     *  - restart if nops > x*codeSize
     *  - use back jumps as loop indicators, restart only if some backjmp is
     *    reduced in size
     *  - don't restart, bet that there's not much more to be done
     */

    if (nops) {
	codeSize = NEW[codeSize];
	goto restart;
    }
}

/*
 * ----------------------------------------------------------------------
 *
 * TclOptimizeBytecode --
 *
 *	A very simple peephole optimizer for bytecode.
 *
 * ----------------------------------------------------------------------
 */

void
TclOptimizeBytecode(
    CompileEnv *envPtr)
{
    int codeSize = (envPtr->codeNext - envPtr->codeStart);
    int NEW[codeSize + 1];

    CompactCode(envPtr, NEW);
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * tab-width: 8
 * End:
 */
