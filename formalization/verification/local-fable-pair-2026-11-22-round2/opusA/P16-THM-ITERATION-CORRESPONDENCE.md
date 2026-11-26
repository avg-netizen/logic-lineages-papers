# P16 `thm:iteration` against `NativeIteratorRealizesFullPrefix` (Opus A, round 2)

## What is compared
- **Printed:** `16-persistent-marking-termination-ordering/sections/ordinals.tex`.
  - Setting at lines 390–399: ι, σ, `E`, `K_i`, `W_i`.
  - Iterator `It_A` at lines 452–456.
  - Convention (I) at lines 457–465.
  - `thm:iteration` and its proof at lines 467–496.
- **Lean, legacy sources:**
  - `LogicLineages/PersistentMarking/NativeOrdinalIterationTargets.lean`: `iteratorShape`, `typedIterator`, `NativeIteratorRealizesFullPrefix`, `NativeIndexedCarrierOrbit`.
  - `OrdinalNativeIterationTargets.lean` (module-system): `OrbitEquations`, `EarlierStages`, `IndexedCarrierRealizesOrbit`.
  - `NativeIteratorTargets.lean`: `iterator`, `iteratorBody`, `eraseBound`, `applied`.
  - `NativeIndexedCarrierTargets.lean`: `discard`, `left`, `K`, `indexedW`, `erase`.
  - `NativeCarrierTargets.lean` (`W`), `NativeReduction.lean` (`recTerm`, `rec2`, `rec1`, `zero`, `app`).
  - `NativeIteratorStrictTargets.lean` (`IteratorNativeStrictChain`, `NativeBelow`).
  - Realization as in `P16-LEM-REALIZATION-CORRESPONDENCE.md`.
- **Compiled:** on twins, in Opus B's gate `1795399156663919873-3256109`, whose root is `NativeModule…NativeOrdinalIterationProof`.
  - Statements: `exact_NativeIteratorRealizesFullPrefix` and `exact_NativeIndexedCarrierOrbit`.
  - Axioms are standard. Peak RSS 929,556 KiB (Opus B's figure).

## Is the Lean iterator literally the printed term?
Printed: `It_A = λi:σ.λp:η.λu:B. R^B 0 (λn:o.((λa:η.λb:η.a)p) E_{A→A}(i)) u`, with `B=|A|`, `η=B→B`, `E_ι(i)=i` and `E_{A→D}(i)=λx:|A|.E_D(i)`.

| Printed piece | Lean | Verdict |
|---|---|---|
| `λi:σ.λp:η.λu:B.` | `iterator A := .lam indexType (.lam (functionType A) (.lam (actualType A) (iteratorBody A)))`, where `indexType = o→o = σ`, `functionType A = B→B = η` and `actualType A = B` | literal |
| `R^B 0 F u` | `recTerm B zero F (.bound B 0)`, where `recTerm τ u A B = app τ τ (rec2 τ u A) B`, `rec2 = app (stepType τ) … (rec1 τ u) A`, `rec1 = app .ground … (.head (.recursor τ) .nil) u` and `zero = .head .zero .nil` | literal. The curried application of the recursor head, with application written as an explicit `.app σ τ` head, which is this syntax's native application. |
| `λn:o.` | `.lam .ground …` | literal |
| `(λa:η.λb:η.a)p` | `left η (.bound η 2)`, where `left η P = app η (η→η) (discard η) P` and `discard η = .lam η (.lam η (.bound η 1))` | literal. `p` has index 2 under `λn`, after `u` (1) and `n` (0). |
| `… E_{A→A}(i)` | `app η η (left η p) (eraseBound (.arrow A A) 3)`, where `eraseBound (.arrow a d) k = .lam |a| (eraseBound d (k+1))` and `eraseBound .base k = .bound indexType k` | literal. `eraseBound` is `E` with the live de Bruijn index of `i` (3 under `λn`), shifted under each new binder. |
| typing | `typedIterator S A := ⟨iterator (nativeShape A), exact_ClosedNativeIterator S (nativeShape A)⟩`, a closed native term of type `σ→η→η` | the printed "closed native iterator" |
| `W_i = R^B0(λn:o.K_i)U` | `indexedW A P U i = W |A| (K A P i) U = recTerm B zero (lifted K) U`, with `lifted K = .lam .ground K` and `K A P i = app η η (left η P) (erase (A→A) i)` | literal. `IteratorLiteralInstantiation` checks that the triple substitution of `(u,p,i)` into `iteratorBody` is exactly `indexedW A p u i`. |

**Verdict: the Lean iterator is the printed term, in locally nameless de Bruijn rendering.**

## Statement
```
NativeIteratorRealizesFullPrefix := ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
  ∀ A, ∃ iterate : Value (iteratorShape A),          -- iteratorShape A = ι → (A→A) → (A→A)
    (∀ f x, OrbitEquations A f x (fun α => iterate α f x)) ∧
    Realizes (nativeTerms S) wf (iteratorShape A) (typedIterator S A) iterate
```

| Printed phrase | Lean | Verdict |
|---|---|---|
| "`It_A` realizes" | `Realizes … (iteratorShape A) (typedIterator S A) iterate`. Unfolded, it reads: `∀ α, ∀ i ⊨ α, ∀ f, ∀ P ⊨ f, ∀ x, ∀ U ⊨ x, It_A i P U ⊨ iterate α f x`, with application `applyClosed`. | exact. It is the printed realization at the curried arrow type: "Fix closed realizers P ⊨ f and U ⊨ x"; `i ⊨ α`. |
| "(α,f,x) ↦ f^α(x)" | `∃ iterate` with `OrbitEquations` at every `f, x` | exact. `OrbitEquations` determines `iterate α f x` uniquely by transfinite induction (`exact_FullPrefixOrbitExists`, `∃!`, in `OrdinalNativeOrbitProof`, generic evidence). The witness used is that orbit, `orbit A f x α`. |
| "for an arbitrary semantic f : A → A" (458) and "even when f is not monotone" | `∀ f : Value A → Value A`, with `Value (A→A)` the full function space and no monotonicity hypothesis anywhere | exact. Non-monotone functions are included. |
| range of α | `α : Value .base = CountableOrdinal`, the ordinals with countable initial segment | **the stated setting, not a restriction.** Line 390: "Let the semantic base type be ι, interpreted as the countable ordinals". Every α the printed theorem speaks of is countable. The realizer side is consistent with this: `r_σ(i)` is a rank over countably many closed terms. |
| all `A` | `∀ A : FiniteType` | exact |
| `f^0(x) = x` | `∀ α, α.val = 0 → orbit α = x` | exact |
| `f^{β+1}(x) = f(f^β(x))` | `∀ α β, β.val = α.val + 1 → orbit β = f (orbit α)` | exact |
| `f^λ(x) = sup_{ξ<λ} f^ξ(x)` (λ > 0 limit) | `∀ lim, Order.IsSuccLimit lim.val → PointwiseSupremum A (fun β : EarlierStages lim => orbit (earlierStage lim β)) (orbit lim)`, with `EarlierStages lim = {β : Ordinal.{0} // β < lim.val}` | exact. The supremum is over the **entire strict prefix**, not a cofinal sequence, which is the "full prefix" of (I). It is pointwise at arrows, as at line 425. `Order.IsSuccLimit` excludes 0 in this Mathlib (`structure IsSuccLimit` requires `¬IsMin`; `Ordinal.not_isSuccLimit_zero`), so "λ > 0 limit" matches. |
| closed native, ranks | `nativeTerms S`, `wf` on `NativeBelow` at σ | exact, as in the realization table |

## Proof, phrase by phrase

| Printed | Lean | Verdict |
|---|---|---|
| "For each closed index i:σ, prove that the single term W_i realizes every x_β for β ≤ r_σ(i)" | `IndexedCarrierRealizesOrbit`: `∀ A f x orbit, OrbitEquations … → ∀ P U i, P ⊨ f → U ⊨ x → ∀ β, β.val ≤ rank i → W A P U i ⊨ orbit β`. Natively this is `NativeIndexedCarrierOrbit`, with carrier `indexedTerm`. | exact |
| "outer well-founded induction on r_σ(i) and inner induction on β" | `exact_IndexedCarrierRealizesOrbit` (generic, #501) | same route |
| "At zero, W_i ⊐ U supplies the conclusion" | the first component of `IndexedCarrierEdges` (#411/#497 subtype edges) and strict backward | same |
| "rank equation gives j with i ⊐ j and r(j) ≥ γ" | `exact_RankImmediateSuccessor` | same |
| "P W_j realizes f(x_γ), and W_i ⊐ P W_j transports" | arrow realization of `P`, then the edge `W_i ⊐ P W_j` with strict backward | same |
| "At a nonzero limit … countably many earlier stages … supremum clause of Lemma realization … entire prefix" | `exact_RealizationCountableSupremum` over `EarlierStages`; countability comes from `CountableOrdinal` | same |
| "If i ⊨ α then α ≤ r_σ(i)" | definitional (`bound := hi`) | same |
| "transport the realization backward through the finitely many beta steps from It_A iPU to this carrier" | `IteratorNativeStrictChain`: `start = applied`, then `afterIndex`, then `afterFunction`, then `final = indexedW A P U i`, with three `NativeBelow` edges. Three explicit `exact_RealizationStrictBackward` steps follow. | same. It is the finite-chain use of `lem:realization`(a), done by hand. |
| "All ranks and edges are those of the closed native confined relation" | `NativeBelow = ConfinedPair.Strict` on `ClosedNativeTerm` | same |

The proof uses `lem:realization` (a) and (c) only. It uses neither (b) nor the lambda clause (d).

**Verdict: the printed theorem, named.** The comparator is `NativeIteratorRealizesFullPrefix`.
- The iterator is the printed term.
- f ranges over all set functions, non-monotone included.
- α ranges over the countable ordinals, which is the paper's stated semantic ι, so there is no restriction.
- The limit stage is the pointwise supremum over the whole earlier prefix, exactly as in (I).

## Twin provenance
- **What was compiled.** As for `lem:realization`: module-system twins by Opus B (`opusB/twin/TWIN-MANIFEST.json`). The proof closure of `NativeOrdinalIterationProof` has 660 modules: 653 twins and 7 module-system originals.
  - 645 twin bodies are byte-identical to the tracked legacy files.
  - 8 have one word `private` deleted. They are `NumberedWindowExternalApplication`, `…ExternalWindowSubstitutionRawProof`, `…PreservationRawProof`, `…PrimarySequenceBaseLift`, `…PrimarySequenceTermLift`, `…RealizationWindowProof`, `…SourceInventoryProof` and `…TraceTypingProof`.
- **Definitions closure.** The closure of the statement definitions, `NativeOrdinalIterationTargets`, has 140 modules. It contains **none** of the eight, checked with `import_graph.closure` on both the legacy and the twin root. All eight are proof-closure helpers only. Every definition in the statement is byte-identical to tracked legacy text: `iterator`, `nativeTerms`, `NativeBelow`, `ConfinedPair.Strict`, `OrbitEquations`, `Realizes`.
- The two `private` helpers of the iteration proof itself (`carrier` and `carrierEdges`) stay private in the twin and do not occur in the statement.
- **Points to weigh before promotion:**
  1. The twins keep the legacy namespaces, so no root may import both copies, and evidence must cite the twin paths.
  2. The legacy iteration and realization roots have never compiled, because of the RSS cap. So this evidence is twin-only, by construction.
  3. `@[expose] public section` makes every twin definition body public, which matches the legacy (non-module) behaviour.
