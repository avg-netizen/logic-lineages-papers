# Actual machine foundation for current19 control hardness

This is supporting work for control-sensitivity.tex, not a replacement for the complete numbered hardness theorem.

## Stage one: exact finite-table bounded simulation

Use the literal existing `SourceBlankMachineSimulation.program : Nat → Table`, `boundedH (e,t) = (simulate e (t+1) []).isSome`, and `Halts` defined by actual TM0 evaluation of the blank configuration. `Table` is a real finite transition table; malformed codes decode to the explicit default. Freeze separate current-source contracts for:

1. Primitive-recursive decoding and surjectivity on actual encoded tables, plus Primrec boundedH.
2. For every e,t, boundedH true iff an actual Run from the blank configuration reaches a step-none state after n<=t transitions. The +1 fuel is final halt observation, not a silently shifted transition bound; zero-step halting is included.
3. Monotonicity in t and actual Halts e iff some boundedH(e,t) is true.
4. Direct instantiation of the already checked full permitted-control target at this very H, with literal gamma definition equality. This pays the H supplier used by the earlier generic result, but has no hardness consequence alone.

Actual current targets should copy the independent semantic propositions, not define Halts as existence of boundedH merely to make correctness reflexive. Every supplier must receive fresh native/import/axiom evidence.

## Stage two: universality and undecidability

The existing blank reduction starts from real Nat.Partrec.Code evaluation, normalizes terminal output and compiles through an actual finite binary alphabet machine. Freeze its genuine effective translator and blank-halting undecidability, then every RE predicate's many-one reduction. Check terminal symbol validation, input specialization, all-code total translator and exact domain equivalence. Do not take undecidable Halts or universal enumeration as an extra caller hypothesis.

## Stage three: same-machine parity

Freeze actual gamma b = control b boundedH, the exact parity identity beyond b, and non-eventual-periodicity at every fixed b. The actual valuationTwo and arithmetic progression must preserve e while tending beyond any true halt time. A putative N,p may be hardwired only in the derived computable halting decider. No eventual-period-finding algorithm is assumed. This supplies the parity clause only, not the full numbered theorem.

## Still separate

Full Pi01 completeness on the printed ground fragment requires literal source addition/constants/S graph, collision and conjunction compiler, effective source representation/typing with only ground free names and binders and internal level<=1, actual canonical evaluation and co-r.e. membership. Source DAG complexity is separate from total computability. No paper20 parked-period route is used or retried. Begin stage-one exact freeze only after conceptual approval.
