/-
  EvmAsm.Rv64.Tactics.PerfTrace

  Trace class hierarchy for profiling the runBlock/seqFrame/xperm tactic pipeline.

  Enable all: `set_option trace.runBlock.perf true`
  Enable subset: `set_option trace.runBlock.perf.perm true`

  Use with `set_option trace.profiler true` for wall-clock timing.
-/

module

public import Lean.Util.Trace
meta import Lean.Util.Trace

@[expose] public section

initialize Lean.registerTraceClass `runBlock.perf (inherited := true)
initialize Lean.registerTraceClass `runBlock.perf.normalize (inherited := true)
initialize Lean.registerTraceClass `runBlock.perf.extend (inherited := true)
initialize Lean.registerTraceClass `runBlock.perf.frame (inherited := true)
initialize Lean.registerTraceClass `runBlock.perf.seq (inherited := true)
initialize Lean.registerTraceClass `runBlock.perf.perm (inherited := true)
initialize Lean.registerTraceClass `runBlock.perf.obligation (inherited := true)
