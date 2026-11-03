# Fixed-window auxiliary primitive reduction

Source: paper06 lines 536–549 restrict the actual all-Mul numbered auxiliary reduction to a fixed finite subtype-closed type universe. The current accepted RawStep is an unrestricted presentation and does not by itself preserve a finite native-head window.

WindowStep and WindowArgumentStep copy every constructor of RawStep and ArgumentStep, respectively. The only added premises are HeadInWindow arity symbols S g at Copy and Mul, where the target introduces g. This window is the already accepted finite symbol/type-list predicate, including original native result and base annotations. All original precedence, head equivalence, occurrence multiset, selected membership, finite labels, ordered extras, binding, beta, bottom and context rules remain literal. There is still no positive reduction in an auxiliary application argument. No target Good predicate or recursively assumed confinement is a rule premise.

The four targets prove actual erasure to the unchanged original raw rules and genuine mutual preservation of InUniverse/GoodArguments under subtype closure. Head-window membership supplies Copy's base-domain types; Select suffix types and finite marking/replacement are derived from accepted primitive suppliers. No decidable equality or stronger ambient-context confinement is required.

This is the restricted primitive relation and its confinement only. Existing raw simulation trace coverage, restricted primary equivalence, finite computable quotient classes, source numerical translation, arithmetic accessibility and whole simulation remain unpaid. The source comparison and its checked transitivity obstruction remain unchanged. Root reviewed the exact constructors and targets on 2026-11-03 before candidate authoring.
