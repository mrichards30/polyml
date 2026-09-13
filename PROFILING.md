# Flame graphs for Poly/ML (and HOL4)

This fork adds **call-stack sampling** to Poly/ML's time profiler, and makes
that profiler work on macOS with Apple Silicon.

Upstream's profiler returns `(count, name)` pairs — a flat list with no caller
information — so there is no way to ask *what was calling* a hot function.
This fork records whole ML stacks and writes them in the folded format that
`flamegraph.pl`, speedscope and the Firefox Profiler all read.

It is inert unless you set an environment variable, so a build of this fork
behaves exactly like upstream until you ask it to profile.

---

## Build it

```sh
git clone https://github.com/mrichards30/polyml
cd polyml
./configure --prefix=$HOME/.local/polyml
make -j10 && make install
```

## Profile anything

Two environment variables:

| variable | effect |
| --- | --- |
| `POLY_PROFILE_OUT=<path>` | profile from RTS startup to shutdown, write the result to `<path>`. `%p` in the path expands to the process id. |
| `POLY_PROFILE_STACKS=1` | record whole call stacks rather than just the function each sample landed in. |

```sh
POLY_PROFILE_STACKS=1 POLY_PROFILE_OUT=/tmp/prof.folded \
    $HOME/.local/polyml/bin/poly < myscript.sml
```

Output is one line per distinct stack:

```
root;...;caller;leaf 42
```

No ML-side wrapper is needed. `PolyML.Profiling.profileStream` can only wrap
code you are in a position to edit, which is no help when a build tool spawns
a process per compilation unit — hence `POLY_PROFILE_OUT` and `%p`.

---

## Profiling a HOL4 build

### 1. Point HOL4 at this Poly/ML

```sh
cd /path/to/HOL
$HOME/.local/polyml/bin/poly < tools/smart-configure.sml
```

**This step is not optional and is easy to skip.** `bin/hol` is a *standalone
image* produced by `polyc` at configure time: it embeds its own copy of the
runtime. Rebuild Poly/ML without re-running `smart-configure` and `bin/hol`
keeps the old runtime, the environment variables below silently do nothing,
and you will conclude the profiler is broken. The only reliable check is
whether a `.folded` file appears.

### 2a. One theory

```sh
cd src/real/analysis
rm -f .hol/objs/real_topologyTheory.*      # force a rebuild
POLY_PROFILE_STACKS=1 POLY_PROFILE_OUT=/tmp/p/%p.folded \
    ../../../bin/Holmake real_topologyTheory.uo
```

### 2b. The whole build

Yes — this works, and it is the interesting case.

```sh
cd /path/to/HOL
bin/build cleanAll
POLY_PROFILE_STACKS=1 POLY_PROFILE_OUT=/tmp/p/%p.folded \
    bin/build < /dev/null
```

A build is made of many short-lived Poly/ML processes — a theory builder per
theory, plus Holmake itself and the heap builds — and that is exactly what
`%p` is for: each writes its own file rather than overwriting the last. The
run used to check this rebuilt 46 theories across **113 processes**, giving
110,413 samples. Merge them and you have a profile of the whole build rather
than of one theory that happened to be convenient to measure.

Note there are more processes than theories, and that `bin/build` only
rebuilds what is out of date — hence the `cleanAll` above if you want the
complete picture.

`< /dev/null` matters for batch runs: `bin/build` sometimes asks you to press
RETURN (for instance when a source file is newer than `bin/hol`), and with no
stdin it will sit there waiting.

### 3. Merge and render

```sh
cat /tmp/p/*.folded | awk '
    { n=$NF; $NF=""; sub(/ $/,""); c[$0]+=n }
    END { for (k in c) print k, c[k] }' > merged.folded

curl -O https://raw.githubusercontent.com/brendangregg/FlameGraph/master/flamegraph.pl
perl flamegraph.pl --title "HOL4 build" --width 1600 merged.folded > build.svg

open build.svg          # macOS; xdg-open on Linux
```

`build.svg` is a self-contained file — open it in any browser, no server or
tooling needed. It carries its own JavaScript: click a frame to zoom into it,
Ctrl-F to search (matches are highlighted and the total is shown), and "Reset
Zoom" to go back. Width is proportional to samples, so the widest boxes are
where the time went; the vertical axis is stack depth, not time.

`merged.folded` also loads directly into
[speedscope](https://www.speedscope.app/) and the Firefox Profiler, both of
which give you zoom, search and an inverted "heaviest stacks" view.

To see just the hottest leaves without rendering anything:

```sh
awk '{ n=$NF; $NF=""; split($0,f,";"); c[f[length(f)]] += n }
     END { for (k in c) printf "%8d  %s\n", c[k], k }' merged.folded |
    sort -rn | head -20
```

---

## Reading the output honestly

**Overhead is roughly 4%** on a HOL4 theory build. Sampling happens every
millisecond per running ML thread.

**Deeply recursive code is over-weighted.** The stack walk runs while the
sampled thread is suspended, so a function with a deep stack is partly charged
for the cost of profiling it. Profile share and wall-clock agree for shallow
code and diverge for deep code — on one HOL4 change, profile share predicted
5.6% and an end-to-end build measured 2.1%, the difference being `List.filter`'s
recursion becoming cheaper to *profile*. Treat shares as a guide to where to
look, and confirm anything you care about with a timed build.

**Some frames genuinely have no caller.** Tail calls destroy the caller's
frame, so roughly one ML sample in forty comes back as a bare leaf. Garbage
collection and RTS phases also appear as single-frame entries — those are
correctly attributed phases, not missing stacks.

**Sampling is only Mach-based on macOS.** Other platforms keep upstream's
`ITIMER_VIRTUAL` path; stack capture works on AArch64.

---

## What changed, and why

Five files under `libpolyml/`, about 650 lines, all additive.

**Correctness, macOS/AArch64.** `Arm64TaskData::AddTimeProfileCount` had
Windows and Linux branches only. On macOS `configure`'s `ucontext_t` probe
fails (the header wants `_XOPEN_SOURCE`), `HAVE_UCONTEXT_T` is undefined,
`SIGNALCONTEXT` degrades to `void`, neither branch compiles, and `pc`/`sp`
stay zero — so every sample missed. Also fixed: `handleProfileTrap` and
`addSynchronousCount` took the same non-recursive lock, so a timer signal
arriving at the wrong moment deadlocked the thread; and an off-by-one in
`processProfileQueue`.

**Sampling.** `ITIMER_VIRTUAL` is delivered at kernel-to-user transitions
rather than where the CPU time was spent. On a HOL4 workload **45% of samples
landed on the single address `__mmap+0x8`**. Sampling now comes from a
dedicated Mach thread reading PC and X28 out of each ML thread that is
actually running. Ticks arriving during an RTS main-thread phase are charged
to that phase, so GC time does not vanish.

**Stack capture.** On AArch64 the ML stack pointer is **X28** — the machine SP
addresses the C stack — and **X30** holds the return address of a leaf that
never spilled it. Both are needed or the walk finds nothing at all. The scan
is conservative, runs while the thread is still suspended (let it run and it
can grow, and therefore move, its own stack mid-scan), and records into a
lock-free ring buffer; names are resolved and stacks folded later on the main
thread.

**Diagnostics.** Unattributable samples used to be reported as `UNKNOWN`. They
are now split into four buckets saying *why*, and a sample whose pc lies
outside ML code is symbolised with `dladdr` and reported as `RTS: <symbol>`
instead of being dropped. Previously a code object with no profile object was
discarded silently, so the counts did not add up to the number of samples
taken.
