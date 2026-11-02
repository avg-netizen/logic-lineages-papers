# Guarded original comparison requests and finite closure

Source paper06 `lem:finiteclosure`, lines151–177. State stores weak/strict mode, actual finite port slots, and two raw packed marked terms. No state or transition requires ordinary targets, membership in the finite observation family, types/heads/names bounds, or successful child comparison. These are intended proved invariants from ordinary root inputs.

The graph keeps actual source guards and candidate data:
- Strict.mark requests the weak marked-source comparison using the real partial strictMark; Weak.put uses its original ordinary head/base and empty extras.
- Weak.abs opens both bodies at one actually unused typed port. Weak.fAbs keeps its literal openMarked construction and appends exactly that fresh variable to extras.
- Weak.fun_ keeps actual equivalent-head and output-type guards, an actual permutation of the entire target argument occurrence list, and candidate paired zip positions.
- Select keeps its exact member/suffix/full-tuple SelectAttempt. Only a real SOME result has a recursive child; IssuedSelect records every original request, including NONE, before any result is known.
- Copy keeps native/user headAbove and requests every actual target argument using the whole source retyped to that argument.
- Stat keeps headEquivalent, source/target occurrence permutations, nonempty removed part, retained zip candidates, and removed×inserted replacement candidates. Side requests retain whole-source retyping. The graph does not demand WeakMatch/ReplacementMatch/Strict child truth as a guard, so failed matching candidates are not excluded.

The deterministic constructors mirror the original recursive clauses; their inclusion is a definitional interface, not an independent semantic achievement. FunPremisesCovered proves actual WeakMatch pairs are real weak premises and graph steps. StatPremisesCovered extracts the actual original StrictMultiset witness and, for every inserted target, an actually chosen removed source with original Strict premise and corresponding strict graph step. This pays the nontrivial occurrence/witness coverage rather than silently replacing multiset matching with set matching.

FreshOpeningAvailability is separate and must derive existence of an unused slot from actual finite target-observation membership. The transition's freshness guard is not used to assume that a required fresh port exists. Frame proves the raw target is the embedding of an actual member of the fixed existing observations list. That list already proves actual port validity, finite syntax membership, target type containment and used-port-plus-remaining-lambda-depth budget.

StepPreservesFrame must pay every original source operation, retaining exact source typeSupport union, literal original-source head membership, original free names plus port binders, and finite target membership. ReachableFrame is then the finite-path induction, explicitly derived rather than advertised as independent source mathematics. IssuedSelectExecutionsBounded combines that invariant with the accepted exact original Apply execution trace, including current original bodies/environments/full tuples, substituted source/base/extras, actual append payloads, and possible failure.

Complete all six targets and review this constructor-to-source coverage before whole finiteclosure adoption. This graph is not itself a terminating comparison algorithm, a finite bound on generated source size, a completeness proof or a replacement ordering. No strong-pair, adequacy or effective-comparison theorem is claimed.
