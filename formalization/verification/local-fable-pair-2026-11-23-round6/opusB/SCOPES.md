# Opus B round-6 scopes (three lines each)

## 1. J closed under multiset union, conditional on its arithmetic — `LogicLineages.NativeModule.PersistentMarking.ConditionalJUnionProof`
- Says: for any presentation data d, outer context c and union program u, if (M7a) the union of two J-carrier codes is a carrier code and (M7b) every direct multiset-replacement step out of a union splits into two components, each unchanged or decreased and at least one decreased, then in the ID₁ calculus J(m), J(n) and U(m,n,o) give J(o), for arbitrary open terms and contexts (`exact_ConditionalJUnion`); the derivation is the printed nested induction (outer J-induction, inner J-induction strengthened by J n).
- Assumes: premises `CarrierUnion d c u`, `MultisetSplit d c u` (derivation-level rules, arithmetic); frozen target sha a5474b2b…4f48; receipt `1795413770153441136-3315432`; axioms propext/Quot.sound.
- Serves: `lem:arithmetic-accessibility` (component "closure of J under multiset union", ordinals.tex 146–152), consumed by "accessible members ⇒ J of their multiset" and constructor induction (L).

## 2. I(q) gives J of its singleton — `LogicLineages.NativeModule.PersistentMarking.ConditionalJSingletonProof` (`exact_ConditionalJSingleton`)
- Says: for any presentation d, context c, union program u and singleton program sg, under the union premises of #1487 and four arithmetic premises (the singleton of an I-carrier element is a J-carrier code; the empty code is a J-carrier code; no replacement step leaves the empty code; a replacement out of the singleton of q is generated from the empty code and the singletons of R_S-descendants of q by union — M7c), the calculus derives J(s) from I(q) and single(q, s), for arbitrary open terms; by I-induction (scalar slice) with the finite union carried by #1487.
- Assumes: `CarrierUnion`, `MultisetSplit`, `SingletonCarrier`, `NilCarrier`, `NilNoStep`, `DescendantGeneration`; frozen target sha cec67446…b867; receipt `1795414175268303942-3316766`; axioms propext/Quot.sound.
- Serves: `lem:arithmetic-accessibility` ("I-induction on Q gives J({Q})", ordinals.tex 152–155).

## 3. Accessible members give J of their multiset — same module (`exact_ConditionalJMembers`)
- Says: under the premises of item 2 and one more (every multiset code is generated from the empty code and the singletons of its members by union), the calculus derives J(m) from ∀x (member(x, m) → I(x)), for arbitrary open m.
- Assumes: the six premises of item 2 and `MemberGeneration`; receipt `1795414175268303942-3316766`; axioms propext/Quot.sound.
- Serves: `lem:arithmetic-accessibility` ("another finite union proves the assertion for arbitrary accessible member multisets", ordinals.tex 155–156), consumed by constructor induction (L).

## 4. Empty multiset is a J-carrier code, for the actual presentation — `LogicLineages.NativeModule.PersistentMarking.ConditionalJNilCarrierProof`
- Says: for every window and checker programs evaluating its original four checks, the calculus derives carrier_J(0) at every outer context (`exact_ActualNilCarrier`); `exact_ActualJSingleton` / `exact_ActualJMembers` are #1489 for those programs with the `NilCarrier` premise removed.
- Assumes: nothing beyond `Evaluates`; frozen target sha 8ad148de…edb6; receipt `1795414761361050081-3319071`; axioms propext/Classical.choice/Quot.sound.
- Serves: `lem:arithmetic-accessibility` (J(∅) in the J-singleton and J-members components).

## 5. Guarded direct checker: admissible, and no step leaves the empty code — `LogicLineages.NativeModule.PersistentMarking.ConditionalJGuardProof`
- Says: for any direct checker program d, the explicit guarded program `guardedDirect d` (0 at source 0, else d) evaluates the window's original direct check whenever d does (`exact_GuardEvaluates`), and on the presentation `data i j r (guardedDirect d)` the calculus refutes every replacement step out of the empty code for open targets (`exact_GuardNilNoStep`); `exact_GuardedJSingleton` / `exact_GuardedJMembers` are #1489 on that presentation without `NilCarrier` and `NilNoStep`. These are statements about the guarded program, a different but equally admissible choice, not about the original existence witness.
- Assumes: `Evaluates` for the original programs (for the evaluation and re-close statements); frozen target sha 4987b507…ec3e; receipt `1795415061808575178-3320260`; axioms propext/Classical.choice/Quot.sound.
- Serves: `lem:arithmetic-accessibility` (J-singleton and J-members components), via the existential program choice of `UniformAccessibility`.
