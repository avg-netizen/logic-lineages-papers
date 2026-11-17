# Proof implementation correspondence

Frozen Source/ComparatorGate are unchanged. ExternalProof is explicitly an intermediate, not the target: accepted compiler and BoxLiteral endpoints require a genuine derivation of the arithmetic guard.

Internalization uses orderGuard's ORIGINAL existential definition. In context ctx+1 the added variable 0 is the gap; every pre-existing inner fuel/certificate, index, raw formula, output certificate, and requested outer fuel is weakened (Fin.succ). Instantiate the external-guard proof at fuel numeral(bound)+var0. The guard is proved directly using orderIntro with witness var0 and reflexive equality. It is NOT obtained from a local hypothesis.

Under orderBody bound outerFuel, actual equality is bound+gap = lift(outerFuel). GuardProof.fuelTransport changes precisely the fuel coordinate of both the CORE and verifier calls. Index/formula/certificate do not change. The composite certificate depends on inner witnesses and source tags but NOT outer fuel or gap. Discharge the weakened original checker-success premise, then orderBody; original existential elimination yields the required guard implication. Its conclusion has been explicitly weakened, so the gap cannot capture any original parameter. Source/certificate naturality and all these operations must compile before acceptance.

Literal encoding uses structural termValue congruence, actual numeralCode computation derivations, and the original closed-substitution encoding theorem. No native calibration is reflected as a source proof; no assertion that distinct raw checker formulas are equal is made. AlgebraProof applies five-coordinate call congruence and transitivity.
