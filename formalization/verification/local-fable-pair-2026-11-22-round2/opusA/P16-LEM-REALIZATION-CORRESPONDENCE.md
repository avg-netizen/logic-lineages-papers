# P16 `lem:realization` against `NativeRealizationClosure ∧ NativeLambdaRealization` (Opus A, round 2)

## What is compared
- **Printed:** `16-persistent-marking-termination-ordering/sections/ordinals.tex`.
  - Rank `r_A` at line 337.
  - Semantic setting at lines 390–391.
  - Realization definition at lines 423–432.
  - `lem:realization` and its proof at lines 434–450.
- **Lean, legacy sources:**
  - `LogicLineages/PersistentMarking/NativeOrdinalRealizationTargets.lean`
  - `LogicLineages/PersistentMarking/OrdinalRealizationTargets.lean` (generic, module-system)
  - Native ingredients: `NativeIteratorStrictTargets` (`ClosedNativeTerm`, `NativeBelow`), `NativeCarrierTargets` (`ClosedNative`), `ConfinedPair` (`Strict`), `NativeClosedApplication` (`applyClosed`), `NativeIndexedCarrierTargets` (`SemanticType`, `indexType`, `actualType`).
- **Compiled:** on the module-system twins (see "Twin provenance").
  - Gate receipt `1795399156663919873-3256109` (Opus B), root `NativeModule…NativeOrdinalIterationProof`. The twin `NativeOrdinalRealizationProof` compiled in its closure.
  - `#print axioms` for both `exact_NativeRealizationClosure` and `exact_NativeLambdaRealization` gives `[propext, Classical.choice, Quot.sound]`.
  - My re-verification gate `1795399550322108167-3260262` covers 536/536 modules, all returncode 0 (verified cache hits).
  - Peak RSS 921,748 KiB, at the realization twin itself.
- **The drafted proof compiled unchanged.** The twin body is byte-identical to the legacy draft, and no repair was needed.

## Definitions (setting)

| Printed phrase | Lean definition | Verdict |
|---|---|---|
| "semantic base type ι, interpreted as the countable ordinals" (390) | `Value .base := CountableOrdinal := {o : Ordinal.{0} // Countable {β // β < o}}` | exact |
| "translate it to the actual type σ = o→o" (390–391) | `actualType .base = indexType = .arrow .ground .ground` | exact |
| "Translate arrows homomorphically" (391) | `actualType (.arrow a d) = .arrow (actualType a) (actualType d)`. Bridged by `nativeShape : FiniteType → SemanticType`; `ExactSemanticShapes` says it is a bijection with inverse `valueShape`. | exact. `ExactSemanticShapes` is bookkeeping between two copies of the same type grammar; no printed counterpart is needed. |
| "Semantic arrow types contain all set functions … not only monotone ones" (424) | `Value (.arrow A D) := Value A → Value D`, the full function space | exact |
| "Countable suprema are pointwise at arrows" (425) | `PointwiseSupremum`: at the base, `α.val = ⨆ i, (f i).val`; at an arrow, `∀ x, PointwiseSupremum D (fun i => f i x) (g x)` | exact |
| "For closed actual terms" (426) | `(nativeTerms S).term A := ClosedNativeTerm S (actualType (nativeShape A)) = {q // ClosedOrdinary S q τ ∧ Native q}` | exact relative to line 337: the printed `r_A` is defined only for closed *native* terms, so "actual" here means closed native. Wording only. |
| `r_σ(t)`: "rank in the restriction of ⊐ to closed native terms of that same type" (337–338) | `(wf.apply t).rank` for `wf : WellFounded (@NativeBelow S indexType)`. Here `NativeBelow target source := ConfinedPair.Strict S source.val target.val`, and `Strict := Domain ∧ Spine.Strict ∧ Included` is the confined strict relation. `Acc.rank t = sup {rank s + 1 : t ⊐ s}`. | exact. `∃ wf` is harmless: `WellFounded` is a Prop, so the rank does not depend on which proof is chosen. |
| `t ⊨_ι α ⟺ r_σ(t) ≥ α` (428) | `Realizes … .base t α := α.val ≤ (wf.apply t).rank` | exact |
| `t ⊨_{A→D} f`: "for every semantic x:A and every closed u ⊨_A x, the ordinary application tu realizes f(x)" (430–432) | `Realizes … (.arrow A D) t f := ∀ x u, Realizes A u x → Realizes D (terms.app A D t u) (f x)`, with `app := applyClosed` = `NativeReduction.app σ τ f a` (the native application head) | exact |
| Signature | `∀ S` outermost. The paper fixes its signature in context. | exact; the Lean is more general |

## Statement, clause by clause

`NativeRealizationClosure := ExactSemanticShapes ∧ PointwiseSupremumExists ∧ ∀ S, ∃ wf, RealizationStrictBackward ∧ RealizationDownward ∧ RealizationCountableSupremum` (all at `nativeTerms S`, `wf`).

**(a) "Realization is preserved when a term is replaced by a strict predecessor."**
- Lean: `RealizationStrictBackward`, `∀ A s t v, below A t s → Realizes A t v → Realizes A s v`, where `below t s` means `s ⊐ t`.
- Verdict: exact, under the reading that "predecessor" means the earlier term in a descending sequence (`s ⊐ t`). That is how the paper uses it: "transports … backward", `W_i ⊐ U`.
- Wording risk: a reader who takes "predecessor" in the rank order (rank-smaller) gets the opposite and false direction. The owner may want "replaced by a term strictly above it".
- `below` holds at every type, not only ι, because `nativeTerms.below := fun _ t s => NativeBelow t s` at `actualType A`. This matches "⊐" on closed native terms of each type.

**(b) "It is downward closed in its semantic value, with pointwise order at arrows."**
- Lean: `RealizationDownward`, `ValueLE A v w → Realizes A t w → Realizes A t v`.
- `ValueLE`: at the base, `α.val ≤ β.val`; at an arrow, `∀ x, ValueLE D (f x) (g x)`.
- Verdict: exact.

**(c) "If one fixed term realizes every member of a nonempty countable family, it realizes their pointwise supremum."**
- Lean: `RealizationCountableSupremum`. For `ι : Type 1` with `[Countable ι] [Nonempty ι]`, a single `t`, a family `f`, and `v` with `PointwiseSupremum A f v`: `(∀ i, Realizes A t (f i)) → Realizes A t v`.
- Separately, `PointwiseSupremumExists` says `∃! v, PointwiseSupremum A f v`, so "their pointwise supremum" is well defined inside `CountableOrdinal` and the function spaces.
- Verdict: exact. The index universe `Type 1` is the one that contains `{β : Ordinal.{0} // β < α}`, which is what `thm:iteration` needs.

**(d) "The typed lambda fundamental lemma holds for these realizers."**
- Lean: `NativeLambdaRealization`:
  ```
  ∀ S, ∃ wf, ∀ A D body (hl : ClosedNative S (.lam |A| body) (|A|→|D|)) (f : Value A → Value D),
    (∀ x (u : term A), Realizes A u x →
       ∃ v : term D, v.val = substitute (.cons u.val .nil) 0 body ∧ Realizes D v (f x)) →
    Realizes (A→D) ⟨.lam |A| body, hl⟩ f
  ```
- Verdict: **not the statement as printed if "fundamental lemma" carries its usual meaning. It is exactly what the printed proof proves.** See the verdict section.

## Proof, phrase by phrase

| Printed proof phrase | Lean (`OrdinalRealizationClosureProof`, generic; `NativeOrdinalRealizationProof`, native) | Verdict |
|---|---|---|
| "Induct on the semantic type." | `exact_RealizationStrictBackward` / `Downward` / `CountableSupremum` over an arbitrary `TermStructure`, by recursion on `FiniteType` (generic record, #498) | same route |
| "At ι, use the rank inequality for a strict edge" | the base case of strict backward: `Acc.rank` of the source exceeds that of the target | same |
| "and the defining property of ordinal supremum" | the base case of the countable supremum, `⨆` over `Ordinal.{0}` | same |
| "At an arrow, apply the induction hypotheses to each realizing argument" | arrow cases, pointwise in `x` and `u` | same |
| "context stability gives tv ⊐ uv from t ⊐ u" | hypothesis `StrictFunctionSlot`, supplied natively by `applicationEdge S := NativeClosedApplicationChecks.exact_NativeApplicationFunctionStrict` (`NativeBelow t s → NativeBelow (applyClosed t a) (applyClosed s a)`) | same content. The printed proof cites the general context stability (`thm:stable`, ordering.tex 214); Lean uses only its application-function instance, which is all the step needs. |
| "The other assertions are pointwise." | arrow cases of `Downward` and `CountableSupremum` | same |
| "For the lambda lemma, its application beta-reduces strictly to the substituted body" | `NativeClosedBetaChecks.exact_ClosedNativeBeta`: `applyClosed ⟨λ,hl⟩ u` reduces to a closed native `result` with `result.val = substitute (u::nil) 0 body` and `NativeBelow result start` | same |
| "so strict predecessor closure transports the body's realization backward" | `exact_RealizationStrictBackward … D start result (f x) edge hClaimed` | same |
| "An induction on the number of beta steps permits any finite sequence." | **No Lean statement.** It is clause (a) iterated along a finite chain of `NativeBelow` edges, a trivial induction on chain length. Every later proof does that iteration by hand: three explicit `backwards` steps in `exact_NativeIteratorRealizesFullPrefix`, and `backwardsTwo` in `exact_ArithmeticRealizationComposition`. | covered by (a) plus a one-line induction. Not stated or gated as a separate statement. |

## The lambda clause: verdict for the owner

**What `NativeLambdaRealization` gives.** It is the *abstraction rule* for one closed native lambda. Suppose that for every semantic `x` and every closed native `u ⊨ x`, the closed substituted body `body[u/0]` realizes `f x`. Then `λ|A|.body ⊨ f`. With (a) iterated, it extends to finite beta chains. Two limits:
- The body's realization is a *hypothesis*, discharged afresh for each closed substitution instance.
- Nothing is said about open terms, about constants, or about a denotation of terms.

**What a full structural fundamental lemma would add.** It would need:
1. A semantic denotation `⟦t⟧ρ ∈ Value A` for *every* native typed term `Γ ⊢ t : A`, including the constants: zero, succ, `case`, the recursor `R^B` at every type, and the comparison heads.
2. The statement: for every closed native substitution `ū` with `u_k ⊨ ρ(x_k)`, `t[ū] ⊨ ⟦t⟧ρ`.
3. The proof: structural induction over open native syntax. Its cases are variable, application (definitional), abstraction (the rule above, under a substitution), and one realization theorem per constant.

The paper defines no such denotation. Its realized values are attached by hand to specific closed abbreviations: `Z`, `s`, `w`, `It_A`, add, mul, pow, fix, `B_l`. The recursor has no general semantic clause. Only `It_A`, a specific use of `R^B`, has a realization theorem (`thm:iteration`). So the general lemma is not merely unproved; its statement is not yet specified in the paper. Stating it is new mathematics, and it is not covered by any record.

**What the later sections use.**
- `thm:iteration` uses (a) and (c) only, plus the native iterator's strict beta chain.
  - It does not use (b) or (d).
  - Checked in Lean: `exact_NativeIteratorRealizesFullPrefix` and `exact_IndexedCarrierRealizesOrbit` invoke only `exact_RealizationStrictBackward` and `exact_RealizationCountableSupremum`.
- The explicit operations `s`, add, mul, one, pow, fix and `w` ("beta transport makes s realize right successor") use the abstraction rule and application.
  - In Lean (`exact_ArithmeticRealizationComposition`), they use (a) along explicit strict beta edges (`ArithmeticStrictEdges`) plus the iterator.
  - That is the abstraction rule unfolded, not a general lemma.
- (B)/(B_T): "The iterator theorem and the lambda fundamental lemma verify the realization of (B)."
  - For each fixed `l`, the closed term `B_l = λh h_l…h_1. fix(λα.(It_{A_l} α h h_l)h_{l-1}…h_1 Z)` is handled by applying the abstraction rule `l+3` times. Each application is to a *closed* substitution instance: substituting a closed realizer into a closed lambda leaves it closed, and `exact_ClosedNativeBeta` supplies the closed result term.
  - Application covers the rest, through the definition of arrow realization, `thm:iteration` at `A_l`, and the realizers `Z` and fix.
  - **No open-term lemma is needed.**
- (D), (R) and `thm:height` need `B_l` for *every* `l`, because `t_n` uses `B_{n-2}, …, B_0`.
  - Doing that uniformly in `l` with only the abstraction rule needs one more induction on `l`. That induction computes de Bruijn substitution into the `B_l` body family.
  - It is syntactic bookkeeping, not a semantic fundamental lemma, but it is not formalized anywhere: no P16 Lean file formalizes (B), (B_T), (D) or (R).

**Verdict.** Under the reading "fundamental lemma = the abstraction rule plus finite beta chains", which is all the printed proof proves and all the later sections use, the clause has an exact comparator: (d) ≅ `NativeLambdaRealization`, with finite chains by iterating (a).
- Under the literal reading (a general structural lemma for all typed terms), the statement is **not comparable** and has no Lean counterpart. The paper also lacks the denotation needed to state it.
- Recommendation: the owner either rewords the last sentence to the abstraction rule, or accepts `NativeLambdaRealization` as its named comparator with this reading recorded.
- Either way, the uniform-in-`l` substitution bookkeeping for (B_T) belongs to the (B)/(D)/(R) step, not to this lemma.

**Overall:** clauses (a), (b) and (c) are exact, with one wording risk in "predecessor". Clause (d) is exact under the abstraction-rule reading and is the owner's decision. The finite-chain sentence is covered by (a) and is not separately stated.

## Twin provenance
- **What was compiled.** The statements were compiled on module-system copies under `LogicLineages/NativeModule/`, generated by Opus B (`opusB/twin/make_twins.py`, manifest `opusB/twin/TWIN-MANIFEST.json`).
  - In the realization proof closure (536 modules), 534 are twins and 2 are module-system originals: `OrdinalRealizationTargets` and `OrdinalRealizationClosureProof`.
  - Each twin has a new header: `module`, `public import` of twin names, and `@[expose] public section`.
  - 526 twin bodies are byte-identical to the tracked legacy files.
  - 8 have one word `private` deleted. They are `NumberedWindowExternalApplication`, `…ExternalWindowSubstitutionRawProof`, `…PreservationRawProof`, `…PrimarySequenceBaseLift`, `…PrimarySequenceTermLift`, `…RealizationWindowProof`, `…SourceInventoryProof` and `…TraceTypingProof`.
  - I re-checked all 534 twin and original shas against the manifest: 0 mismatches.
- **Definitions closure.** The closure of the statement definitions, `NativeOrdinalRealizationTargets`, has 50 modules: 48 legacy plus the 2 module-system originals. It contains **none** of the eight edited files, checked with `import_graph.closure` on both the legacy and the twin root. All eight lie only in the proof closure, as helpers of the numbered-window proofs. So every definition used in `NativeRealizationClosure` and `NativeLambdaRealization` is byte-identical to the tracked legacy text.
- **Points to weigh before promotion:**
  1. Twins keep the original namespaces, so twin and legacy declare the same constant names. No root may import both, and a promotion must cite the twin module paths.
  2. `@[expose] public section` exposes every definition body. This preserves the legacy definitional behaviour and is what the proofs rely on.
  3. A deleted `private` can change nothing about a statement here. It only widens visibility of a proof helper, and a name clash would have failed compilation.
  4. The realization proof itself was never compiled as a legacy file: the legacy root hit the 1,536 MiB cap. So its evidence is twin-only.

## Lane actions under this task (before the scope change)
- I wrote no twin `.lean` files. My adapted generator copy, `opusA/twin/make_twins.py` (skip-existing), wrote 0 twins and listed all 534 as `skipped_existing` in `opusA/twin/TWIN-MANIFEST-REALIZATION.json`.
- I ran two verifying gates, both cache hits only, with nothing compiled:
  - `1795399532290638667-3260157`: the three `NativeClosed*Checks` twins, 532 modules.
  - `1795399550322108167-3260262`: the realization proof twin, 536 modules.
