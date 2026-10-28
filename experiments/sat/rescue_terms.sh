#!/bin/sh
# Copy the term list out of a running cut_ground/box_cut process into a checkpoint pickle, without stopping it.
# gdb waits for the next entry into pysat's solve (a clean point: the GIL is held, no C code is mid-operation),
# runs a few lines of Python there, and detaches.   usage: rescue_terms.sh PID OUT.ckpt
PID=$1; OUT=$(realpath -m "$2")
cat > ${TMPDIR:-/tmp}/rescue_$$.py <<PY
import sys, pickle, os
f = sys._getframe()
while f is not None and not (type(f.f_locals.get('G')).__name__ == 'Ground'): f = f.f_back
if f is None: open('$OUT.err', 'w').write('no Ground in the frame stack\n')
else:
    G = f.f_locals['G']
    with open('$OUT.tmp', 'wb') as fh: pickle.dump(list(G.terms), fh)
    os.replace('$OUT.tmp', '$OUT')
PY
gdb -p "$PID" -batch -nx \
  -ex 'set breakpoint pending on' \
  -ex 'break py_cadical153_solve' -ex 'break py_cadical195_solve' \
  -ex 'continue' -ex 'set scheduler-locking on' \
  -ex 'delete' \
  -ex 'call (int) PyGILState_Ensure()' \
  -ex "call (int) PyRun_SimpleString(\"exec(open('${TMPDIR:-/tmp}/rescue_$$.py').read())\")" \
  -ex 'call (void) PyGILState_Release($1)' \
  -ex 'detach' -ex 'quit' > ${TMPDIR:-/tmp}/rescue_$$.gdb.log 2>&1
rm -f ${TMPDIR:-/tmp}/rescue_$$.py
if [ -s "$OUT" ]; then python3 -c "import pickle,sys; print('rescued', len(pickle.load(open(sys.argv[1],'rb'))), 'terms to', sys.argv[1])" "$OUT"
else echo "failed; see ${TMPDIR:-/tmp}/rescue_$$.gdb.log"; cat "$OUT.err" 2>/dev/null; fi
