/*
    Title:      Profiling
    Author:     Dave Matthews, Cambridge University Computer Laboratory

    Copyright (c) 2000-7
        Cambridge University Technical Services Limited
    Further development copyright (c) David C.J. Matthews 2011, 2015, 2020-21

    This library is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public
    License version 2.1 as published by the Free Software Foundation.
    
    This library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.
    
    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA

*/

#ifdef HAVE_CONFIG_H
#include "config.h"
#elif defined(_WIN32)
#include "winconfig.h"
#else
#error "No configuration file"
#endif

#ifdef HAVE_STDLIB_H
#include <stdlib.h>
#endif

#ifdef HAVE_MALLOC_H
#include <malloc.h>
#endif

#ifdef HAVE_ASSERT_H
#include <assert.h>
#define ASSERT(x) assert(x)
#else
#define ASSERT(x) 0
#endif

#include "globals.h"
#include "arb.h"
#include "processes.h"
#include "polystring.h"
#include <unistd.h>
#include "profiling.h"
#include "save_vec.h"
#include "rts_module.h"
#include "memmgr.h"
#include "scanaddrs.h"
#include "locking.h"
#include "run_time.h"
#include "sys.h"
#include "rtsentry.h"
#include "machine_dep.h"
#include "polystring.h"

#if defined(HAVE_DLFCN_H) || defined(__APPLE__)
#include <dlfcn.h>
#define POLY_HAVE_DLADDR 1
#endif

extern "C" {
    POLYEXTERNALSYMBOL POLYUNSIGNED PolyProfiling(POLYUNSIGNED threadId, POLYUNSIGNED mode);
}

static long mainThreadCounts[MTP_MAXENTRY];
static const char* const mainThreadText[MTP_MAXENTRY] =
{
    "UNKNOWN",
    "GARBAGE COLLECTION (sharing phase)",
    "GARBAGE COLLECTION (mark phase)",
    "GARBAGE COLLECTION (copy phase)",
    "GARBAGE COLLECTION (update phase)",
    "GARBAGE COLLECTION (minor collection)",
    "Common data sharing",
    "Exporting",
    "Saving state",
    "Loading saved state",
    "Profiling",
    "Setting signal handler",
    "Cygwin spawn",
    "Storing module",
    "Loading module",
    "Releasing module",
    "UNATTRIBUTED (signal hit a non-ML thread)",
    "UNATTRIBUTED (ML thread, no ML pc: in the RTS)",
    "UNATTRIBUTED (ML pc, no code object)",
    "UNATTRIBUTED (code object, no profile object)"
};

// Entries for store profiling
enum _extraStore {
    EST_CODE = 0,
    EST_STRING,
    EST_BYTE,
    EST_WORD,
    EST_MUTABLE,
    EST_MUTABLEBYTE,
    EST_MAX_ENTRY
};

static POLYUNSIGNED extraStoreCounts[EST_MAX_ENTRY];
static const char * const extraStoreText[EST_MAX_ENTRY] =
{
    "Function code",
    "Strings",
    "Byte data (long precision ints etc)",
    "Unidentified word data",
    "Unidentified mutable data",
    "Mutable byte data (profiling counts)"
};

// Poly strings for "standard" counts.  These are generated from the C strings
// above the first time profiling is activated.
static PolyWord psRTSString[MTP_MAXENTRY], psExtraStrings[EST_MAX_ENTRY], psGCTotal;

ProfileMode profileMode;
// If we are just profiling a single thread, this is the thread data.
static TaskData *singleThreadProfile = 0;

// The queue is processed every 400ms and an entry can be
// added every ms of CPU time by each thread.
#define PCQUEUESIZE 4000

#define RTSQUEUESIZE 4000
#define RTSTABSIZE   256
static POLYCODEPTR rtsQueue[RTSQUEUESIZE];
static long rtsQueuePtr = 0;
static struct { char name[96]; POLYUNSIGNED count; } rtsTab[RTSTABSIZE];
static unsigned rtsTabUsed = 0;

#define STACKQ_SIZE 2000
#define FOLDTAB_SIZE 8192
static struct { int n; POLYCODEPTR pcs[STACK_MAXDEPTH]; } stackQueue[STACKQ_SIZE];
static long stackQueuePtr = 0;
static struct { char *key; POLYUNSIGNED count; } foldTab[FOLDTAB_SIZE];
static unsigned foldTabUsed = 0;

static long queuePtr = 0;
static POLYCODEPTR pcQueue[PCQUEUESIZE];
static PLock queueLock;

typedef struct _PROFENTRY
{
    POLYUNSIGNED count;
    PolyWord functionName;
    struct _PROFENTRY *nextEntry;
} PROFENTRY, *PPROFENTRY;

class ProfileRequest: public MainThreadRequest
{
public:
    ProfileRequest(unsigned prof, TaskData *pTask):
        MainThreadRequest(MTP_PROFILING), mode(prof), pCallingThread(pTask), pTab(0), errorMessage(0) {}
    ~ProfileRequest();
    virtual void Perform();
    Handle extractAsList(TaskData *taskData);

public:
    void getResults(void);
private:
    void getProfileResults(PolyWord *bottom, PolyWord *top);
    PPROFENTRY newProfileEntry(void);

private:
    unsigned mode;
    TaskData *pCallingThread;
public:
    PPROFENTRY pTab;
private:

public:
    const char *errorMessage;
};

ProfileRequest::~ProfileRequest()
{
    PPROFENTRY p = pTab;
    while (p != 0)
    {
        PPROFENTRY toFree = p;
        p = p->nextEntry;
        free(toFree); 
    }
}

// Lock to serialise updates of counts. Only used during update.
// Not required when we print the counts since there's only one thread
// running then.
static PLock countLock;

// Atomic updates for the profiling counts.  These must be safe to use from a
// signal handler: handleProfileTrap can interrupt a thread that is already
// holding countLock or queueLock, so taking either lock there can deadlock the
// thread against itself.  Follows the same portability pattern as
// atomiclySetForwarding in quick_gc.cpp.
static void atomicIncrementCount(long *addr)
{
#ifdef _MSC_VER
    InterlockedIncrement((LONG*)addr);
#elif defined(__GNUC__)
    __sync_fetch_and_add(addr, 1);
#else
    // Fallback where no atomic primitive is available.  Not signal-safe.
    PLocker lock(&countLock);
    (*addr)++;
#endif
}

static long atomicFetchAndAdd(long *addr, long incr)
{
#ifdef _MSC_VER
    return (long)InterlockedExchangeAdd((LONG*)addr, (LONG)incr);
#elif defined(__GNUC__)
    return __sync_fetch_and_add(addr, incr);
#else
    // Fallback where no atomic primitive is available.  Not signal-safe.
    PLocker lock(&countLock);
    long old = *addr;
    *addr += incr;
    return old;
#endif
}

// Get the profile object associated with a piece of code.  Returns null if
// there isn't one, in particular if this is in the old format.
static PolyObject *getProfileObjectForCode(PolyObject *code)
{
    ASSERT(code->IsCodeObject());
    PolyWord *consts;
    POLYUNSIGNED constCount;
    machineDependent->GetConstSegmentForCode(code, consts, constCount);
    if (constCount < 2 || consts[1].AsUnsigned() == 0 || ! consts[1].IsDataPtr()) return 0;
    PolyObject *profObject = consts[1].AsObjPtr();
    if (profObject->IsMutable() && profObject->IsByteObject() && profObject->Length() == 1)
        return profObject;
    else return 0;
}

// Adds incr to the profile count for the function pointed at by
// pc or by one of its callers.
void addSynchronousCount(POLYCODEPTR fpc, POLYUNSIGNED incr)
{
    // Check that the pc value is within the heap.  It could be
    // in the assembly code.
    PolyObject *codeObj = gMem.FindCodeObject(fpc);
    if (codeObj)
    {
        PolyObject *profObject = getProfileObjectForCode(codeObj);
        if (profObject)
        {
            PLocker locker(&countLock);
            profObject->Set(0, PolyWord::FromUnsigned(profObject->Get(0).AsUnsigned() + incr));
        }
        else
            // Previously this sample was dropped silently, so the counts did
            // not add up to the number of samples taken.
            atomicIncrementCount(&mainThreadCounts[MTP_UNATTR_NOPROFOBJ]);
    }
    // Didn't find it.
    else
        atomicIncrementCount(&mainThreadCounts[MTP_UNATTR_NOCODEOBJ]);
}


// newProfileEntry - Make a new entry in the list
PPROFENTRY ProfileRequest::newProfileEntry(void)
{
    PPROFENTRY newEntry = (PPROFENTRY)malloc(sizeof(PROFENTRY));
    if (newEntry == 0) { errorMessage = "Insufficient memory"; return 0; }
    newEntry->nextEntry = pTab;
    pTab = newEntry;
    return newEntry;
}

// We don't use ScanAddress here because we're only interested in the
// objects themselves not the addresses in them.
// We have to build the list of results in C memory rather than directly in
// ML memory because we can't allocate in ML memory in the root thread.
void ProfileRequest::getProfileResults(PolyWord *bottom, PolyWord *top)
{
    PolyWord *ptr = bottom;

    while (ptr < top)
    {
        ptr++; // Skip the length word
        PolyObject *obj = (PolyObject*)ptr;
        if (obj->ContainsForwardingPtr())
        {
            // This used to be necessary when code objects were held in the
            // general heap.  Now that we only ever scan code and permanent
            // areas it's probably not needed.
            while (obj->ContainsForwardingPtr())
                obj = obj->GetForwardingPtr();
            ASSERT(obj->ContainsNormalLengthWord());
            ptr += obj->Length();
        }
        else
        {
            ASSERT(obj->ContainsNormalLengthWord());

            if (obj->IsCodeObject())
            {
                PolyWord *firstConstant = machineDependent->ConstPtrForCode(obj);
                PolyWord name = firstConstant[0];
                PolyObject *profCount = getProfileObjectForCode(obj);
                if (profCount)
                {
                    POLYUNSIGNED count = profCount->Get(0).AsUnsigned();
                
                    if (count != 0)
                    {
                        if (name != TAGGED(0))
                        {
                            PPROFENTRY pEnt = newProfileEntry();
                            if (pEnt == 0) return;
                            pEnt->count = count;
                            pEnt->functionName = name;
                        }
                    
                        profCount->Set(0, PolyWord::FromUnsigned(0));
                    }
                }
            } /* code object */
            ptr += obj->Length();
        } /* else */
    } /* while */
}

void ProfileRequest::getResults(void)
// Print profiling information and reset profile counts.
{
    for (std::vector<PermanentMemSpace*>::iterator i = gMem.pSpaces.begin(); i < gMem.pSpaces.end(); i++)
    {
        MemSpace *space = *i;
        // Permanent areas are filled with objects from the bottom.
        getProfileResults(space->bottom, space->top); // Bottom to top
    }
    for (std::vector<CodeSpace *>::iterator i = gMem.cSpaces.begin(); i < gMem.cSpaces.end(); i++)
    {
        CodeSpace *space = *i;
        getProfileResults(space->bottom, space->top);
    }

    {
        POLYUNSIGNED gc_count =
            mainThreadCounts[MTP_GCPHASESHARING]+
            mainThreadCounts[MTP_GCPHASEMARK]+
            mainThreadCounts[MTP_GCPHASECOMPACT] +
            mainThreadCounts[MTP_GCPHASEUPDATE] +
            mainThreadCounts[MTP_GCQUICK];
        if (gc_count)
        {
            PPROFENTRY pEnt = newProfileEntry();
            if (pEnt == 0) return; // Report insufficient memory?
            pEnt->count = gc_count;
            pEnt->functionName = psGCTotal;
        }
    }

    for (unsigned k = 0; k < MTP_MAXENTRY; k++)
    {
        if (mainThreadCounts[k])
        {
            PPROFENTRY pEnt = newProfileEntry();
            if (pEnt == 0) return; // Report insufficient memory?
            pEnt->count = mainThreadCounts[k];
            pEnt->functionName = psRTSString[k];
            mainThreadCounts[k] = 0;
        }
    }

    for (unsigned l = 0; l < EST_MAX_ENTRY; l++)
    {
        if (extraStoreCounts[l])
        {
            PPROFENTRY pEnt = newProfileEntry();
            if (pEnt == 0) return; // Report insufficient memory?
            pEnt->count = extraStoreCounts[l];
            pEnt->functionName = psExtraStrings[l];
            extraStoreCounts[l] = 0;
        }
    }
}

// Extract the accumulated results as an ML list of pairs of the count and the string.
Handle ProfileRequest::extractAsList(TaskData *taskData)
{
    Handle saved = taskData->saveVec.mark();
    Handle list = taskData->saveVec.push(ListNull);

    // folded call stacks (flamegraph input)
    for (unsigned k = 0; k < foldTabUsed; k++)
    {
        if (foldTab[k].count == 0) continue;
        Handle nameH = taskData->saveVec.push(C_string_to_Poly(taskData, foldTab[k].key));
        Handle pair = alloc_and_save(taskData, 2);
        Handle countValue = Make_arbitrary_precision(taskData, foldTab[k].count);
        pair->WordP()->Set(0, countValue->Word());
        pair->WordP()->Set(1, nameH->Word());
        Handle next = alloc_and_save(taskData, sizeof(ML_Cons_Cell) / sizeof(PolyWord));
        DEREFLISTHANDLE(next)->h = pair->Word();
        DEREFLISTHANDLE(next)->t = list->Word();
        taskData->saveVec.reset(saved);
        list = taskData->saveVec.push(next->Word());
        foldTab[k].count = 0;
    }

    // RTS symbols resolved from samples outside ML code
    for (unsigned k = 0; k < rtsTabUsed; k++)
    {
        if (rtsTab[k].count == 0) continue;
        char buff[128];
        buff[0] = 0;
        strncat(buff, "RTS: ", sizeof(buff) - 1);
        strncat(buff, rtsTab[k].name, sizeof(buff) - strlen(buff) - 1);
        Handle nameH = taskData->saveVec.push(C_string_to_Poly(taskData, buff));
        Handle pair = alloc_and_save(taskData, 2);
        Handle countValue = Make_arbitrary_precision(taskData, rtsTab[k].count);
        pair->WordP()->Set(0, countValue->Word());
        pair->WordP()->Set(1, nameH->Word());
        Handle next = alloc_and_save(taskData, sizeof(ML_Cons_Cell) / sizeof(PolyWord));
        DEREFLISTHANDLE(next)->h = pair->Word();
        DEREFLISTHANDLE(next)->t = list->Word();
        taskData->saveVec.reset(saved);
        list = taskData->saveVec.push(next->Word());
        rtsTab[k].count = 0;
    }

    for (PPROFENTRY p = pTab; p != 0; p = p->nextEntry)
    {
        Handle pair = alloc_and_save(taskData, 2);
        Handle countValue = Make_arbitrary_precision(taskData, p->count);
        pair->WordP()->Set(0, countValue->Word());
        pair->WordP()->Set(1, p->functionName);
        Handle next  = alloc_and_save(taskData, sizeof(ML_Cons_Cell) / sizeof(PolyWord));
        DEREFLISTHANDLE(next)->h = pair->Word();
        DEREFLISTHANDLE(next)->t =list->Word();

        taskData->saveVec.reset(saved);
        list = taskData->saveVec.push(next->Word());
    }

    return list;
}

// We have had an asynchronous interrupt and found a potential PC but
// we're in a signal handler.
void incrementCountAsynch(POLYCODEPTR pc)
{
    // Called from a signal handler: must not take queueLock.
    long q = atomicFetchAndAdd(&queuePtr, 1);
    if (q < PCQUEUESIZE) pcQueue[q] = pc;
}

// ---- RTS sample attribution -------------------------------------------
// Samples whose pc lies outside any ML space used to be discarded as
// "UNKNOWN" (or, worse, guessed at from the stack).  They are a large
// fraction of a real profile - 20% for a HOL4 theory - so queue the raw
// address here and resolve it to a C symbol when the queue drains.

void recordRTSSample(POLYCODEPTR pc)
{
    // Called from the signal handler: no locks, no allocation.
    long q = atomicFetchAndAdd(&rtsQueuePtr, 1);
    if (q < RTSQUEUESIZE) rtsQueue[q] = pc;
}

static void drainRTSQueue()
{
    long n = rtsQueuePtr;
    if (n <= 0) return;
    if (n > RTSQUEUESIZE) n = RTSQUEUESIZE;
    for (long i = 0; i < n; i++)
    {
        const char *nm = "RTS (unresolved)";
#ifdef POLY_HAVE_DLADDR
        Dl_info info;
        char tmp[96];
        if (dladdr((void*)rtsQueue[i], &info) != 0 && info.dli_sname != 0)
        {
            snprintf(tmp, sizeof(tmp), "%s+0x%lx", info.dli_sname,
                     (unsigned long)((const char*)rtsQueue[i] -
                                     (const char*)info.dli_saddr));
            nm = tmp;
        }
#endif
        unsigned k;
        for (k = 0; k < rtsTabUsed; k++)
            if (strcmp(rtsTab[k].name, nm) == 0) break;
        if (k == rtsTabUsed)
        {
            if (rtsTabUsed >= RTSTABSIZE) continue;   // table full; drop
            strncpy(rtsTab[k].name, nm, sizeof(rtsTab[k].name) - 1);
            rtsTab[k].name[sizeof(rtsTab[k].name) - 1] = 0;
            rtsTab[k].count = 0;
            rtsTabUsed++;
        }
        rtsTab[k].count++;
    }
    rtsQueuePtr = 0;
}


// ---- folded stack profiling ------------------------------------------
// Poly/ML's profile is flat: a sample bumps a counter on the code object it
// landed in, so there is no call-hierarchy information and hot shared leaves
// cannot be attributed.  With a real pc and sp (see arm64.cpp) the ML stack
// can be scanned conservatively for return addresses, giving a whole stack per
// sample.  Stacks are folded to "leaf;caller;caller2" and counted, which is
// the input format flamegraph.pl expects.
bool profileStacksWanted()
{
    static int want = -1;
    if (want < 0) {
        want = (getenv("POLY_PROFILE_STACKS") != 0) ? 1 : 0;
    }
    return want != 0;
}

void recordStackSample(POLYCODEPTR *pcs, int n)
{
    long q = atomicFetchAndAdd(&stackQueuePtr, 1);
    if (q >= STACKQ_SIZE) return;
    if (n > STACK_MAXDEPTH) n = STACK_MAXDEPTH;
    stackQueue[q].n = n;
    for (int i = 0; i < n; i++) stackQueue[q].pcs[i] = pcs[i];
}

static bool nameOfCode(POLYCODEPTR pc, char *buff, size_t bufflen)
{
    PolyObject *codeObj = gMem.FindCodeObject(pc);
    if (codeObj == 0) return false;
    if (!codeObj->IsCodeObject()) return false;
    PolyWord *firstConstant = machineDependent->ConstPtrForCode(codeObj);
    PolyWord name = firstConstant[0];
    if (name == TAGGED(0) || !name.IsDataPtr()) return false;
    Poly_string_to_C(name, buff, (POLYUNSIGNED)bufflen);
    return true;
}

static void drainStackQueue()
{
    long n = stackQueuePtr;
    if (n <= 0) return;
    if (n > STACKQ_SIZE) n = STACKQ_SIZE;
    for (long i = 0; i < n; i++)
    {
        char names[STACK_MAXDEPTH][128];
        int nn = 0;
        for (int f = 0; f < stackQueue[i].n; f++)
        {
            char nm[128];
            if (!nameOfCode(stackQueue[i].pcs[f], nm, sizeof(nm)))
            {
                // Only the leaf is worth symbolising outside ML: a sample
                // taken in the RTS still belongs under its ML caller, so
                // dropping it would hide GC and allocation from the graph.
                if (f != 0) continue;
                const char *rn = 0;
#ifdef POLY_HAVE_DLADDR
                Dl_info info;
                if (dladdr((void*)stackQueue[i].pcs[0], &info) != 0 &&
                    info.dli_sname != 0)
                    rn = info.dli_sname;
#endif
                nm[0] = 0;
                strncat(nm, "RTS: ", sizeof(nm) - 1);
                strncat(nm, rn != 0 ? rn : "unresolved",
                        sizeof(nm) - strlen(nm) - 1);
            }
            // Poly/ML leaves several return addresses per activation on the
            // stack, so the same function shows up in consecutive frames.
            // Collapsing them also collapses self-recursion, which is what a
            // flame graph wants anyway.
            if (nn > 0 && strcmp(names[nn-1], nm) == 0) continue;
            strncpy(names[nn], nm, sizeof(names[0]) - 1);
            names[nn][sizeof(names[0]) - 1] = 0;
            nn++;
            if (nn >= STACK_MAXDEPTH) break;
        }
        if (nn == 0) continue;

        // flamegraph.pl wants root first; the scan produced leaf first.
        char folded[STACK_MAXDEPTH * 128];
        folded[0] = 0;
        for (int f = nn - 1; f >= 0; f--)
        {
            if (folded[0] != 0)
                strncat(folded, ";", sizeof(folded) - strlen(folded) - 1);
            strncat(folded, names[f], sizeof(folded) - strlen(folded) - 1);
        }

        unsigned k;
        for (k = 0; k < foldTabUsed; k++)
            if (strcmp(foldTab[k].key, folded) == 0) break;
        if (k == foldTabUsed)
        {
            if (foldTabUsed >= FOLDTAB_SIZE) continue;
            foldTab[k].key = strdup(folded);
            if (foldTab[k].key == 0) continue;
            foldTab[k].count = 0;
            foldTabUsed++;
        }
        foldTab[k].count++;
    }
    stackQueuePtr = 0;
}

// Called by the main thread to process the queue of PC values
void processProfileQueue()
{
    drainRTSQueue();
    drainStackQueue();
    while (1)
    {
        POLYCODEPTR pc = 0;
        {
            PLocker locker(&queueLock);
            if (queuePtr == 0) return;
            // queuePtr counts the entries written, so the newest is at
            // queuePtr-1.  Indexing with queuePtr itself read one slot beyond
            // the data, losing the entry at index 0 and counting a stale pc.
            if (queuePtr <= PCQUEUESIZE)
                pc = pcQueue[queuePtr - 1];
            atomicFetchAndAdd(&queuePtr, -1);
        }
        if (pc != 0)
            addSynchronousCount(pc, 1);
        else
            atomicIncrementCount(&mainThreadCounts[MTP_UNATTR_NOCODEOBJ]);
    }
}

// Handle a SIGVTALRM or the simulated equivalent in Windows.  This may be called
// at any time so we have to be careful.  In particular in Linux this may be
// executed by a thread while holding a mutex so we must not do anything, such
// calling malloc, that could require locking.
void handleProfileTrap(TaskData *taskData, SIGNALCONTEXT *context)
{
    if (singleThreadProfile != 0 && singleThreadProfile != taskData)
        return;

    if (mainThreadPhase == MTP_USER_CODE)
    {
        if (taskData == 0)
            atomicIncrementCount(&mainThreadCounts[MTP_UNATTR_NOTASK]);
        else if (!taskData->AddTimeProfileCount(context))
            atomicIncrementCount(&mainThreadCounts[MTP_UNATTR_NOMLPC]);
        // On Mac OS X all virtual timer interrupts seem to be directed to the root thread
        // so all the counts will be "unknown".
    }
    else
        atomicIncrementCount(&mainThreadCounts[mainThreadPhase]);
}

// Called from the GC when allocation profiling is on.
void AddObjectProfile(PolyObject *obj)
{
    ASSERT(obj->ContainsNormalLengthWord());
    POLYUNSIGNED length = obj->Length();

    if ((obj->IsWordObject() || obj->IsClosureObject()) && OBJ_HAS_PROFILE(obj->LengthWord()))
    {
        // It has a profile pointer.  The last word should point to the
        // closure or code of the allocating function.  Add the size of this to the count.
        ASSERT(length != 0);
        PolyWord profWord = obj->Get(length-1);
        ASSERT(profWord.IsDataPtr());
        PolyObject *profObject = profWord.AsObjPtr();
        ASSERT(profObject->IsMutable() && profObject->IsByteObject() && profObject->Length() == 1);
        profObject->Set(0, PolyWord::FromUnsigned(profObject->Get(0).AsUnsigned() + length + 1));
    }
    // If it doesn't have a profile pointer add it to the appropriate count.
    else if (obj->IsMutable())
    {
        if (obj->IsByteObject())
            extraStoreCounts[EST_MUTABLEBYTE] += length+1;
        else extraStoreCounts[EST_MUTABLE] += length+1;
    }
    else if (obj->IsCodeObject())
        extraStoreCounts[EST_CODE] += length+1;
    else if (obj->IsByteObject())
    {
        // Try to separate strings from other byte data.  This is only
        // approximate.
        if (OBJ_IS_NEGATIVE(obj->LengthWord()))
            extraStoreCounts[EST_BYTE] += length+1;
        else
        {
            PolyStringObject *possString = (PolyStringObject*)obj;
            POLYUNSIGNED bytes = length * sizeof(PolyWord);
            // If the length of the string as given in the first word is sufficient
            // to fit in the exact number of words then it's probably a string.
            if (length >= 2 &&
                possString->length <= bytes - sizeof(POLYUNSIGNED) &&
                possString->length > bytes - 2 * sizeof(POLYUNSIGNED))
                    extraStoreCounts[EST_STRING] += length+1;
            else
            {
                extraStoreCounts[EST_BYTE] += length+1;
            }
        }
    }
    else extraStoreCounts[EST_WORD] += length+1;
}

// Called from ML to control profiling.
static Handle profilerc(TaskData *taskData, Handle mode_handle)
/* Profiler - generates statistical profiles of the code.
   The parameter is an integer which determines the value to be profiled.
   When profiler is called it always resets the profiling and prints out any
   values which have been accumulated.
   If the parameter is 0 this is all it does, 
   if the parameter is 1 then it produces time profiling,
   if the parameter is 2 it produces store profiling.
   3 - arbitrary precision emulation traps. */
{
    unsigned mode = get_C_unsigned(taskData, mode_handle->Word());
    {
        // Create any strings we need.  We only need to do this once but
        // it must be done by a non-root thread since it needs a taskData object.
        // Don't bother locking.  At worst we'll create some garbage.
        for (unsigned k = 0; k < MTP_MAXENTRY; k++)
        {
            if (psRTSString[k] == TAGGED(0))
                psRTSString[k] = C_string_to_Poly(taskData, mainThreadText[k]);
        }
        for (unsigned k = 0; k < EST_MAX_ENTRY; k++)
        {
            if (psExtraStrings[k] == TAGGED(0))
                psExtraStrings[k] = C_string_to_Poly(taskData, extraStoreText[k]);
        }
        if (psGCTotal == TAGGED(0))
            psGCTotal = C_string_to_Poly(taskData, "GARBAGE COLLECTION (total)");
    }
    // All these actions are performed by the root thread.  Only profile
    // printing needs to be performed with all the threads stopped but it's
    // simpler to serialise all requests.
    ProfileRequest request(mode, taskData);
    processes->MakeRootRequest(taskData, &request);
    if (request.errorMessage != 0) raise_exception_string(taskData, EXC_Fail, request.errorMessage);
    return request.extractAsList(taskData);
}

POLYUNSIGNED PolyProfiling(POLYUNSIGNED threadId, POLYUNSIGNED mode)
{
    TaskData *taskData = TaskData::FindTaskForId(threadId);
    ASSERT(taskData != 0);
    taskData->PreRTSCall();
    Handle reset = taskData->saveVec.mark();
    Handle pushedMode = taskData->saveVec.push(mode);
    Handle result = 0;

    try {
        result = profilerc(taskData, pushedMode);
    } catch (...) { } // If an ML exception is raised

    taskData->saveVec.reset(reset);
    taskData->PostRTSCall();
    if (result == 0) return TAGGED(0).AsUnsigned();
    else return result->Word().AsUnsigned();
}

// This is called from the root thread when all the ML threads have been paused.
void ProfileRequest::Perform()
{
    if (mode != kProfileOff && profileMode != kProfileOff)
    {
        // Profiling must be stopped first.
        errorMessage = "Profiling is currently active";
        return;
    }

    singleThreadProfile = 0; // Unless kProfileTimeThread is given this should be 0

    switch (mode)
    {
    case kProfileOff:
        // Turn off old profiling mechanism and print out accumulated results 
        profileMode = kProfileOff;
        processes->StopProfiling();
        getResults();
        // Remove all the bitmaps to free up memory
        gMem.RemoveProfilingBitmaps(); 
        break;

    case kProfileTimeThread:
        singleThreadProfile = pCallingThread;
        // And drop through to kProfileTime
      
    case kProfileTime:
        profileMode = kProfileTime;
        processes->StartProfiling();
        break;

    case kProfileStoreAllocation:
        profileMode = kProfileStoreAllocation;
        break;
        
    case kProfileEmulation:
        profileMode = kProfileEmulation;
        break;

    case kProfileLiveData:
        profileMode = kProfileLiveData;
        break;
 
    case kProfileLiveMutables:
        profileMode = kProfileLiveMutables;
        break;

    case kProfileMutexContention:
        profileMode = kProfileMutexContention;
        break;
       
    default: /* do nothing */
        break;
    }

}

struct _entrypts profilingEPT[] =
{
    // Profiling
    { "PolyProfiling",                  (polyRTSFunction)&PolyProfiling},

    { NULL, NULL} // End of list.
};


class Profiling: public RtsModule
{
public:
    virtual void Init(void);
    virtual void Start(void);
    virtual void Stop(void);
    virtual void GarbageCollect(ScanAddress *process);
};

// Declare this.  It will be automatically added to the table.
static Profiling profileModule;

void Profiling::Init(void)
{
    // Reset profiling counts.
    profileMode = kProfileOff;
    for (unsigned k = 0; k < MTP_MAXENTRY; k++) mainThreadCounts[k] = 0;
}

// Profiling a whole process without touching the program being profiled.
// PolyML.Profiling.profileStream can only wrap ML code you are able to edit;
// a HOL4 theory is built by a fresh poly process per theory, launched by
// Holmake, so there is nowhere to put the wrapper.  Setting POLY_PROFILE_OUT
// to a file name profiles from RTS startup to shutdown and writes the result
// there.  With POLY_PROFILE_STACKS also set the output is folded call stacks
// ("root;...;leaf count"), which is flamegraph.pl's input format.
static bool wholeProcessProfile = false;

void Profiling::Start(void)
{
    const char *out = getenv("POLY_PROFILE_OUT");
    if (out == 0 || *out == 0) return;
    wholeProcessProfile = true;
    profileMode = kProfileTime;
    processes->StartProfiling();
}

void Profiling::Stop(void)
{
    // Not gated on profileMode: Processes::Stop runs before this one and
    // clears it.
    const char *out = getenv("POLY_PROFILE_OUT");
    if (!wholeProcessProfile || out == 0 || *out == 0) return;
    wholeProcessProfile = false;
    profileMode = kProfileOff;
    processes->StopProfiling();
    // Samples queued by the sampler thread have not been folded yet.
    drainStackQueue();
    drainRTSQueue();

    // A build spawns one process per theory, all inheriting this variable, so
    // "%p" in the name expands to the pid and keeps them apart.
    char path[1024];
    const char *pct = strstr(out, "%p");
    if (pct != 0)
        snprintf(path, sizeof(path), "%.*s%d%s", (int)(pct - out), out,
                 (int)getpid(), pct + 2);
    else
    {
        path[0] = 0;
        strncat(path, out, sizeof(path) - 1);
    }

    FILE *f = fopen(path, "w");
    if (f == 0) return;

    for (unsigned k = 0; k < foldTabUsed; k++)
        if (foldTab[k].count != 0)
            fprintf(f, "%s %" POLYUFMT "\n", foldTab[k].key, foldTab[k].count);
    for (unsigned k = 0; k < rtsTabUsed; k++)
        if (rtsTab[k].count != 0)
            fprintf(f, "RTS: %s %" POLYUFMT "\n", rtsTab[k].name, rtsTab[k].count);

    // The phase counts are normally turned into ML strings on the way out to
    // ML; nothing has done that here, so write them from the C table and
    // clear them before getResults sees them.
    for (unsigned k = 0; k < MTP_MAXENTRY; k++)
    {
        if (mainThreadCounts[k] == 0) continue;
        fprintf(f, "%s %ld\n", mainThreadText[k], mainThreadCounts[k]);
        mainThreadCounts[k] = 0;
    }

    // The per-code-object counts are only filled in by getResults.
    ProfileRequest req(0, 0);
    req.getResults();
    for (PPROFENTRY p = req.pTab; p != 0; p = p->nextEntry)
    {
        char buff[256];
        if (p->functionName == TAGGED(0) || !p->functionName.IsDataPtr()) continue;
        Poly_string_to_C(p->functionName, buff, sizeof(buff));
        fprintf(f, "%s %" POLYUFMT "\n", buff, p->count);
    }
    fclose(f);
}

void Profiling::GarbageCollect(ScanAddress *process)
{
    // Process any strings in the table.
    for (unsigned k = 0; k < MTP_MAXENTRY; k++)
        process->ScanRuntimeWord(&psRTSString[k]);
    for (unsigned k = 0; k < EST_MAX_ENTRY; k++)
        process->ScanRuntimeWord(&psExtraStrings[k]);
    process->ScanRuntimeWord(&psGCTotal);
}
