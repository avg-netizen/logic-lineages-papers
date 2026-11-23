# Paper 16 `thm:upper`: printed proof vs the chain compiled on the module copies (Opus B, round 3)

Reading only, no gates. Printed source is `16-persistent-marking-termination-ordering/sections/ordinals.tex` (lines given
below). Lean names are read from the definitions. Twin modules are `LogicLineages.NativeModule.PersistentMarking.<M>`;
their declaration names are those of the legacy originals, `LogicLineages.PersistentMarking.<M>.<decl>`.
Records cited: #489 well-foundedness, #1448 rank-dominance wrapper and native ranks, #1454 scalar stage norm,
#1455 class rank = address rank = stage norm.

## 1. Statement (l. 315–318)

| printed | Lean | verdict |
|---|---|---|
| "The confined strict relation is well founded" | `NumberedWindowExternalWellFoundedTargets.ConfinedStrictWellFounded` := `∀ S, WellFounded (fun t s => ConfinedPair.Strict S s t)`; #489 | carried |
| "rk_cs(s) < BH for every ordinary term s" | no Lean statement: BH has no definition in the repository | **open** |

## 2. Proof, step by step (l. 319–333)

| # | printed phrase | Lean carrier | verdict |
|---|---|---|---|
| P1 | "Every descendant of s remains in S = Ty(s)" | `NumberedWindowConfinedRankMapTargets.InitialConfinedWindowGuard`: a typed ordinary q gives `Closed (TypeSupport.support q)` and a `start : GuardedTerm S (support q) τ` with `start.val = q`. `ConfinedPredecessorInGuard`: `Guard S K τ q → Strict S q t → Guard S K τ t` (#1448 closure, checked earlier as #521) | carried, with K = `support q` = Ty(s) |
| P2 | "Lemmas arithmetic-accessibility and positive-simulation exclude an infinite strict chain" | Not formalized this way. Well-foundedness is proved externally (#488/#489) from the external computability argument (#486/#487), not from an ID₁ proof | carried by a different route; the printed route uses the open lemma |
| P3 | "positive-edge simulation gives rk_cs(s) ≤ rk_{R_S}(tr s)" | `NumberedWindowConfinedRankDominanceProof.exact_OriginalInitialQuoteRankDominance : OriginalInitialQuoteRankDominance`. For every S, q, τ with `PaperTerm S q τ` and `Ordinary q` there exist `start`, `symbolicWF`, `numericalWF` with `start.val = q` and `(symbolicWF.apply q).rank ≤ (numericalWF.apply (quote start)).rank`. Here `numericalWF : WellFounded (FixedPositiveBelow S (support q) τ)` and `FixedPositiveBelow S K τ t s := RS S K EmptyContext τ s t`. The guarded form is `exact_ConfinedRankBelowFixedQuote` (#1448) | carried, provided `quote start` = tr(s) (§3) |
| P4a | "The arithmetic accessibility proof supplies an ID₁ proof of the individual I-membership of tr(s)" | **none**; see §4 R1 | **open** |
| P4b | "The tagged I component has its standalone accessibility norm" | Two pieces. (i) `NumberedWindowAddressClassRankProof.exact_ActualAddressClassRankEquality`: for `q : Class S K (finiteC Γ) τ`, `classAcc.rank = addressAcc.rank` for `Acc (AddressBelow S K) (classAddress hk q)` (#1455). (ii) `exact_ActualClassStageNormAtAddress`: that rank `IsLeast` among the ordinals a with `ordinalStage (scalarStep S K) a (classAddress hk q)`, and likewise for `taggedStep S K` at `tagScalar (classAddress hk q)` (#1455, using #1454 `exact_ActualScalarOrdinalNorm`, `exact_ActualScalarStageRank`). Stages are `NumberedWindowExternalIDStages.stage` over `Ordinal.{0}`, as least fixed points of the operator from below, matching "stages beginning at the operator applied to the empty set" (`exact_StageStartsAtOperatorEmpty`) | carried for the **semantic** operators `scalarStep`/`taggedStep`; the bridge to the syntactic ID₁ body is in §4 R2 |
| P4c | "Applying the published norm theorem yields rk_{R_S}(tr s) < BH" | **none** (§4 R2) | **open, external** |
| P5 | "No transitivity assumption … is needed" | consistent: `RS` is the positive-path closure (`RS.one`, `RS.more`) and rank maps use only edges | n/a |

Joining P3 to P4b takes Γ = []. `finiteC [] = BoundContext.prefix [] EmptyContext` reduces to `EmptyContext` by
the first clause of `prefix`, so `Class S K EmptyContext τ` and `Class S K (finiteC []) τ` are the same type
definitionally. `hk` comes from P1. **No single compiled theorem states the composite**
"rank of q ≤ least stage of `taggedStep (support q)` at `tagScalar (classAddress hk (quote start))`". The composition is a
few lines of assembly, unwritten.

The other #1448 statements (`NativeRankChecks.*`, `NativeRankUnconditionalChecks.exact_ActualClosedNativeRanks`:
native rank recurrence, strict edge, restriction ≤ confined rank, successor witness, ranks < ω₁) concern closed
**native** terms. They serve `thm:height`'s lower bound, not `thm:upper`.

## 3. Is `quote start` the printed tr(s)?

Printed (l. 229–233). q ∼_n Q when Q realizes q "with the same typed shape, ordinary heads at label ω, and every marked
head at some finite label at least n". "For an ordinary q there is a unique tr(q)". R_S is the positive-path relation of
raw ⇝ on classes of the head-equivalence/permutation congruence in the fixed window (l. 70–76). The window is
"precisely Ty(s)" (l. 302).

Lean:
- `NumberedWindowOrdinaryTranslation.tr : Spine.Expr → Option NTerm` is literal and constructor by constructor: free and
  bound variables map to themselves, lambdas map to `.lam`, and `.head f bs` maps to `.ordinary f (trArgs bs)`.
  `.ordinary` is the numerical constructor whose label is implicitly ω (NumberedWindowSyntax). On `.marked` it returns
  `none`, matching "for an ordinary q".
- `NumberedWindowConfinedRankMap.quote q := classOf ⟨Classical.choose h, _⟩`, where
  `h : ∃ Q, tr q.val = some Q ∧ InWindow S K EmptyContext τ Q` (`exact_OrdinaryQuoteInSuppliedWindow`).
  Choice is harmless here, because `tr` is a function. `NumberedWindowConfinedRankMapTargets.GuardedQuoteLiteral`
  (proved as `NumberedWindowConfinedRankMapChecks.exact_GuardedQuoteLiteral`, compiled in the #1448 closure) states `tr q.val = some Q → quote q = classOf ⟨Q, hQ⟩`.
- `classOf` is the quotient by `NumberedWindowPrimary.Primary` on `WindowCarrier S K C τ = {Q // InWindow S K C τ Q}`.
  `InWindow` means typed in C at τ, type support ⊆ K, and every head `HeadInWindow S K`. `RS` is the transitive
  closure of `ClassEdge` (one actual `RawStep` between representatives).
- The window is K = `TypeSupport.support q` (P1), the bound context is `EmptyContext`, and the type is the fixed type τ.

**Verdict: the printed tr(s), taken as its class in a named restriction of R_S.** The construction is the printed one:
ordinary heads at ω, identity on variables and lambdas, the same window Ty(s). The relation is the printed R_S
**restricted to classes of the single type τ in the empty bound context**, with Primary as the head congruence.

Two caveats, neither a mismatch in the construction:
- (a) Rank in this restriction equals the printed rank only because every raw descendant keeps type, context and window.
  This is the content of `lem:window-locality` (#439) and of the typed `RawStep`. I found no compiled statement saying
  "rank in the fixed-τ restriction = rank in the whole R_S universe". The address relation `AddressBelow` of #1455
  ranges over all (Γ, τ) and agrees with the fixed-τ class rank by `exact_ActualAddressClassRankEquality`. So for the
  norm only the address rank matters, and the caveat is harmless downstream.
- (b) That `Primary` is exactly the printed head-replacement/permutation congruence is not re-examined here. It is the
  same quotient used by the accepted `lem:positive-simulation` (#438) and `lem:tuple-simulation` (#425).

## 4. What remains for `thm:upper`

**R1: internal accessibility I(tr s).** The object calculus is
`ID1Completion.InternalCalculus.Derivation (body : Positive (Fin 1)) Γ φ` (InternalCalculusDefinitions l. 79).
The body is `ID1Completion.SourcePresentation.sourceBody (data pI pJ pR pD) c`. Its data come from the four checker
programs (`NumberedWindowInternalPresentationTargets.data`; programs #563, calibrated #560/#564). The statement to
derive is either:
- the individual atom: `Nonempty (Derivation (sourceBody d c) [] (Positive.predicate (tagTerm false (numeral n))).formula)`
  for n = the address of tr(s) at window S, K = Ty(s), with d the #563 programs. This is exactly printed P4a.
- or, uniformly: `Nonempty (Derivation (sourceBody d c) [] (allTermsFormula d c))`, the all-terms sentence. Its
  standard-model truth is accepted (#567/#569/#573). Its derivability is `lem:arithmetic-accessibility`, for every
  admitted address of every window.

Internal pieces that exist are #571 (both (A) equations), #578/#582 ((T) and arrow rules), #585/#599 (conditional),
and #1457 plus the sparse-decode ID₁ graph lemmas (`NumberedWindowInternalSparseDecodeChecks.exact_OpenSuccess`/`exact_OpenFailure`).
Missing: forward matching, typed-probe totality (`NumberedWindowInternalFreshProbeDispatchOriginalIntegrationTargets`,
definitions only), the neutral lemma, the lambda fact, J closure, (L), and the final structural induction.

**R2: the external norm theorem (Pohlers, Defs 6.3.1, 6.3.5, 9.1.2, Lemma 6.5.2, Thms 9.5.5–9.5.6).** A Lean statement
would read, for every positive body B and every n:
`Nonempty (Derivation B [] (Positive.predicate (numeral n)).formula) → ∃ a < BH, stage (<) Ordinal.lt_wf (operatorOf B) a n`.
It must mention three ingredients:
- **The theory ID₁.** It exists: `Derivation` with its arithmetic and induction rules (`naturalInductionSchema`,
  `ArithmeticInstance`) plus the body's closure and induction rules. Whether this calculus is literally Pohlers' ID₁
  (language, induction scheme for formulas with the I-predicate, strictly positive operator form) is an
  owner-level correspondence check; I made none.
- **The stage norm of the tagged operator.** It exists for **semantic** operators: `NumberedWindowExternalIDStages.stage`
  and `taggedStep S K`, with norm = rank by #1454/#1455. Not found: a definition `operatorOf B` sending a syntactic
  positive body to its operator `fun P n => realize P B.formula ![n]`, and a proof that the stages of
  `operatorOf (sourceBody d c)` equal those of `taggedStep S K`. That proof should follow pointwise from
  `NumberedWindowInternalPresentationTargets.TaggedSemantics` and the checker calibration (#560/#563). It is small,
  but unwritten.
- **BH.** It does **not** exist. The repository has no Bachmann–Howard ordinal, no ψ/Ω collapse and no
  ordinal-notation system above Γ₀. Pinned Mathlib has `SetTheory/Ordinal/Veblen.lean` (Veblen hierarchy, Γ₀) and
  fixed points, nothing more. Without such a definition, R2 cannot even be stated, let alone accepted as an
  external citation. A minimal path would be an owner-approved definition of BH (e.g. ψ_Ω(ε_{Ω+1}) via a chosen
  collapse) plus R2 as an explicitly cited, unproved hypothesis.

**Residual summary.** Two items remain: R1, the ID₁ derivation of the I-atom at tr(s)'s address (a case of
`allTermsFormula` derivability); and R2, Pohlers' norm bound for `Derivation`-provable atoms. R2 needs a BH that does
not exist, and a small syntactic-to-semantic stage bridge that has not been written. A short assembly lemma
(P3 ∘ P4b at Γ = []) is also missing.
