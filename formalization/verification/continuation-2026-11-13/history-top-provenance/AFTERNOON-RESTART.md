# Afternoon continuation after restart

Recovered original frozen targets and draft helpers. Compiler coordinator reports
helper gate 1794593742482874510-5 passed for InductionBinding, EntryWitnessProof,
ConsInjectiveProof and ActiveStepProof. Later OutputRestProof and KeepCasesProof
passed in gate 1794594073825786273-5, whose aggregate stopped in KeepOptionsProof.
A focused successor-substitution repair is now submitted for the full exact3.
Do not treat the aggregate as accepted until its final receipt is verified.

The full candidate uses a simpler invariant than the original auxiliary seven-
argument universal induction. For a fixed target state and witness formula Q,
every actual kernel preserves `(state = target -> Q)`. Empty input is identity;
NONE with a nonempty input cannot yield SOME; SOME with a nonempty input gives
a new witness from the actually consumed line. Internal decoder reconstruction
covers every raw state code. Ordinary internal arithmetic induction on the
actual iterator count then proves the original arbitrary-count target.

The witness asserts nonzero actual v, not v=1. No native calibration, Boolean
range, line-field invariance, source tuple identity, HB rule, or completed paper
is inferred. Auxiliary induction binding/zero modules are retained but not needed
by the final candidate. The source register is unchanged.

## Resource diagnosis

The first positive-lines candidate repeatedly reached the fixed RSS cap. Splitting
its reconstruction and formula-transport suppliers gave independently checked
small modules, but did not fix the caller. Source review then identified a local
`a` term shadowing the input arithmetic Program `a`: the allOptions invocation
was accidentally supplied a Term where a Program was required. That unification
mismatch plausibly triggered the excessive reduction. The local terms are now
named `decodedLeft` and `decodedRight`; no resource limits, statement premises,
or frozen target bytes changed. Failed variants remain archived. Acceptance of
the corrected full candidate still awaits the coordinator's final exact gate.
