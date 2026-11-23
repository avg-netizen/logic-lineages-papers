# Paper 16 gap map: the eight pending statements (Opus B, 22 Nov, reading only)

The register `CURRENT-COMPARISON-TARGETS.json` lists 8 pending Paper 16 labels, 30 checked of 38. Each pending entry has no
`formal_target` field. Line numbers refer to `../16-persistent-marking-termination-ordering/`. Records are under
`verification/new-paper-set-2026-11-18/accepted/`, and `recovery-nov19/` is short for `…/paper16/recovery-nov19/`. "Not found"
means a search of the record scopes, the paper16 notes and the two 22 Nov handoffs found nothing. This file contains no gates
and no proofs. It was measured with `import_graph.py` and file greps only.

Classes: **A** assembly of checked pieces · **N** new mathematics · **I** infrastructure · **M** blocked on the manuscript ·
**X** external literature not formalized.

## 1. lem:structural-interpretation (decision.tex 149): class M; Lean work after that is A

Statement: the interpreter and the original-spine helper are monotone and commute with weakening. The interpreter respects
capture-avoiding substitution. For environments that interpret concrete substitutions, the helper interprets full application of
the substituted source, undefined cases included. Proof: simultaneous induction on the source and the helper.

| clause | cover |
|---|---|
| monotone, natural under weakening (interpreter and helper) | #394 (environments #388, scoped agreement #395) |
| capture-avoiding free substitution | #396, first half |
| bound (simultaneous) substitution | #397 |
| helper interprets full application, including undefined | **false as printed**: #396 second half is a counterexample. #398 proves it at a **fixed point** of the operator |

The correction is in `recovery-nov19/MANUSCRIPT-CORRECTION-HANDOFF.md`, unapplied. (1) At decision.tex 149–155 the
full-application clause needs an explicit fixed-point qualification. The counterexample sits at the bottom retained family.
There, the helper's output for ordinary successor applied to a covered ground variable differs from the interpretation of the
successful marked call result. (2) At decision.tex 228–230, the adequacy proof uses this lemma inside stage induction. Adding
fixedness does not repair that use. The handoff says to use the hereditary relation and stagewise soundness route instead
(#413–#415), and already accepted adequacy and decision (#415, #416) do so. Once the owner amends clause (1) to "at a fixed
point", the statement is a conjunction alias over #394 ∧ #396 ∧ #397 ∧ #398. That alias is probably one combined core gate. Its
size was not measured.

## 2. lem:realization (ordinals.tex 434): classes I + A, and possibly N for the lambda clause

Statement: realization is (a) preserved under strict predecessor, (b) downward closed in value, pointwise at arrows, and (c)
closed under countable pointwise suprema by one fixed term. (d) The "typed lambda fundamental lemma holds". Proof: induction on
the semantic type. At ι it uses the rank inequality and the ordinal sup. At an arrow it uses context stability, tv ⊐ uv. For the
lambda part: beta is strict, so (a) transports the realization of the body backward, and induction on the number of beta steps
handles finite sequences.

- (a)–(c) generic: #498, and `OrdinalRealizationTargets` / `OrdinalRealizationClosureProof` (module-system Mathlib). The native
  ingredients are checked separately: closed native beta is strict (#496), the indexed-carrier edges lie in the rank subtype
  (#497), and context stability is `thm:stable`.
- The native instance `NativeOrdinalRealizationTargets.NativeRealizationClosure` is **drafted, never gated**. It is a legacy
  root, and the measured stop was RSS 1,573,864 kB against a 1,572,864 kB cap.
- (d): `NativeLambdaRealization` (same file) is the abstraction rule. If every realizing argument u gives a substituted body
  that realizes f x, then the lambda realizes f. It is drafted, not gated. `NATIVE-ORDINAL-REALIZATION-HANDOFF.md` says "the
  general structural typed fundamental lemma remains open". **Observation:** the printed proof of (d) proves only the
  abstraction rule plus finite beta chains. It never proves a general "every typed term under a realizing substitution realizes
  its denotation". The towers (B_T)/(D) are built from closed abbreviations, and term by term they need only the abstraction
  rule plus application. If the comparator for (d) is the abstraction rule, then (d) is assembly once the infrastructure lands.
  If the owner wants the general lemma, that lemma is new mathematics. It means structural induction over open native typed
  syntax with a realizing substitution, which no record covers.
- Infrastructure: target closure 50 local modules (48 legacy, all core-only). The proof closure
  (`NativeOrdinalRealizationProof`) has 536 modules: 534 legacy, 2 module-system. See §9.

## 3. thm:iteration (ordinals.tex 467): classes I + A

Statement: It_A realizes (α,f,x) ↦ f^α(x) under convention (I), with f possibly non-monotone. Proof: carrier W_i realizes x_β
for β ≤ r_σ(i). Outer induction on r_σ(i), inner induction on β. At zero, W_i ⊐ U. At a successor, the rank equation gives a
child j with i ⊐ j and r(j) ≥ γ, and P W_j realizes f(x_γ) and transports back. At a limit, the realization-sup clause over the
whole prefix applies. Then α ≤ r_σ(i), and the result transports back over the finite beta steps from It_A i P U.

- The generic orbit and the carrier induction are #501 (`OrdinalIndexedCarrierOrbitProof`, module-system). Native carrier:
  `lem:carrier` #407, `lem:indexed-carrier` #411, subtype edges #497. The strict iterator beta chain is in
  `NATIVE-ITERATOR-STRICT-HANDOFF.md` and `NativeIteratorStrict*` (22-module closure).
- Missing: only the native specialization `NativeOrdinalIterationTargets`/`Proof` (drafted). It needs lem:realization (a)+(c),
  not (d). Target closure: 140 modules (138 legacy). Proof closure: 660 (653 legacy, 7 module-system). No new mathematics was
  found.

## 4. lem:arithmetic-accessibility (ordinals.tex 79): class N (large); the printed proof is entirely internal ID₁

Statement: for fixed S and 𝓕, ID₁ proves I(Q) for every well-typed auxiliary Q under R_S. The truth of this statement in the
standard model is already checked externally: #486 covers (L) and the neutral lemma,
#487 the structural induction, and #573 standard-model truth of the all-terms sentence. The pending item is
**ID₁-provability**. Internal object-calculus counterparts of the printed steps:

| printed step | internal counterpart |
|---|---|
| (A) operators I and J, tagged into one positive definition | **yes**: #571, both (A) equations on open terms, carrier extraction, successor closure, introduction |
| (T) computability by type, first-order in I | **yes**: #578 formulas over the canonical application graph. #579 shows the standard reading equals the quotient computability. #582 gives arrow intro/elim and commutation of (T) with substitution |
| joint type induction: downward closure of (T) along R_S | **conditional**: #585, given the open "uniform matching derivation" |
| computable ⇒ I at arrows (fresh x, Qx R_S Q'x, induction on I(Qx)) | **conditional**: #599, scalar least induction, given forward matching. Fresh variable computable: only at ground (#662); #631–#644 each say "no neutral computability" |
| neutral lemma (non-lambda with computable reducts is computable; variables, bottom) | **none** |
| lambda fact (substitution turns a raw step into a path or equality; induction on I(V)) | **none**. #582 commutes (T) with substitution, not raw steps |
| J closed under multiset union (nested J-induction), J({Q}) from I(Q) | **none**. The "J" in #1243–#1284 is the argument-list grammar J(G), not the DM(R_S) operator |
| constructor induction (L) over (head class, base multiset, label ∈ ℕ∪{ω}, extras) | **none** internally (external #486) |
| final structural induction under computable substitution | **none** internally (external #487) |

Where today's results sit. They all serve the open "matching" premise of #585/#599. In the class-address encoding, the printed
fact "Qx R_S Q'x from Q R_S Q'" has to become "application on canonical classes is a well-defined, accepted operation that is
compatible with R_S edges":
- #1419–#1421: an edge between functions gives an application-level measured edge. The application least is constant on a
  function's reached pool over the measured exchange.
- #1422 class congruence: the same packed least for the functions gives the same application least.
- #1430: one route installs the measured exchange in edge, members, least, scalar and frontend.
- #1431/#1432: application least **existence** from the type guards and windows, then from the installed acceptances.
- #1438 accepted output address. #1440 the installed application program accepts the (function, argument, output) triple.

So application is now a total, accepted, class-invariant operation on installed addresses, up to the two type guards. None of
this yet gives the matching statement itself.

Next internal statements, in order (vocabulary of `NumberedWindowInternalCoverCombinedMeasuredInstall` and
#585):
1. **Forward matching, open terms.** Take accepted installed addresses f, g with an accepted positive edge or path f → g at one
   context, and an accepted argument a. Then the output addresses of f·a and g·a (from #1440) are equal or joined by an accepted
   positive path. When f and g share a packed least this is #1422. The edge case across classes is the step that is missing.
   #606 proved it for numerals only.
2. **Discharge the two syntax/refit type guards internally** from the typed address, or get the owner to accept them as
   calibration. They are held in every record from #1419 to #1440.
3. Instantiate the #585 and #599 premises with 1–2. This gives internal downward closure of (T) and computable ⇒ I, provided
   fresh variables are computable at arrow types, which is the neutral lemma at variables.
4. Internal **neutral lemma**. This needs an internal enumeration of the direct reducts of an application under the eight raw
   rules. Their checker exists as a program (#560/#563), but no internal reduct-exhaustion lemma exists.
5. Internal **lambda fact**: a raw step under substitution becomes a raw path or equality, derived in ID₁.
6. Internal **J union closure** and J({Q}) from I(Q).
7. Internal **(L)**: a four-level nested induction covering every raw rule, including Select, Copy, the multiset rule,
   abstraction creation, lowering and bottom.
8. Internal **structural induction** under computable substitution, then the conclusion.

Distance: of the nine printed components, two have unconditional internal counterparts ((A), (T) with arrow rules) and two are
conditional on item 1. P16 supporting records #1117–#1440 (177 records) all sit at or below item 1. Items 4–8 are each
comparable in size to the whole matching effort, and none has been started. Estimate: several rounds for item 1 and many rounds
for the lemma. "Not reachable at the current granularity" is a fair reading. Consequence for priorities: see thm:upper. Even a
finished internal proof yields the BH bound only through the unformalized Pohlers norm theorem.

## 5. thm:upper (ordinals.tex 315): first conjunct done; rank domination gated on twins; rest needs I + N + X

Statement: the confined strict relation ⊐ is well founded, and rk_cs(s) < BH. Proof: Lem arithmetic-accessibility plus Lem
positive-simulation exclude infinite chains. The simulation gives rk_cs(s) ≤ rk_{R_S}(tr s). The ID₁ proof of I(tr s), together
with the published norm theorem, gives rk_{R_S}(tr s) < BH.

- Well-foundedness: #489 ("first conjunct of thm:upper"), via #488 and `lem:positive-simulation` #438.
- Rank domination rk_cs(s) ≤ rk_{R_S}(tr s): **gated on the twins (update, 22 Nov)**, receipt
  `1795399872966250102-3264833` (first compiled in `1795399748659677836-3263981`), peak RSS 906,532 KiB. Twin
  `NumberedWindowConfinedRankDominanceProof`: `exact_OriginalInitialQuoteRankDominance`. For every typed ordinary q there
  is a guarded start with `start.val = q` and (symbolic rank of q) ≤ (rank of `quote start` in the fixed-window positive
  relation R_S). `exact_ConfinedRankBelowFixedQuote` is its guarded form. Axioms: propext, Classical.choice, Quot.sound.
  It combines #521 and #522; whether `quote start` matches the printed tr(s) is a correspondence question for the owner.
- Still missing for the second conjunct, in proof order:
  1. **R_S rank = I-norm.** The class rank under R_S equals the stage norm of the tagged ID₁ operator at the canonical
     address ("the tagged I component has its standalone accessibility norm"). This step is **drafted, never compiled**,
     and parked behind the import boundary: `NumberedWindowAddressClassRankTargets/Proof`
     (`ActualAddressClassRankEquality`, `ActualClassStageNormAtAddress`) and `NumberedWindowGuardedNormTargets/Proof`
     (`ActualScalarStageRank`, `ActualScalarOrdinalNorm`). No accepted record pins them and no local receipt shows them
     compiled. Class: I, plus whatever repair the drafts need. The rank modules this round needed two small proof repairs.
  2. **ID₁ proof of I(tr s)**: §4. Class: N, large.
  3. **Pohlers's norm theorem**, and with it a Lean definition of BH: see below. Class: X.
  So Root's expectation is **confirmed with one correction**: besides the internal ID₁ proof and Pohlers, thm:upper also
  needs step 1. That step is a parked draft, not new mathematics.
- ID₁ proof of I(tr s): §4. Class: N.
- Norm theorem (Pohlers, Defs 6.3.1, 6.3.5, 9.1.2, Lemma 6.5.2, Thms 9.5.5–9.5.6): ID₁-provable positive memberships have
  inductive norm < BH. **Not found** anywhere in the Lean tree: no Bachmann–Howard, ψ-collapse, Ω-based notation or infinitary
  ID₁ calculus. The only "Bachmann" hit is a Paper 06 source comment. Pinned Mathlib has `SetTheory/Ordinal/Veblen.lean` and
  `FixedPoint.lean` (nfp/deriv) but nothing above Γ₀ of collapsing type. Class: X, of very large size: an ordinal analysis of
  ID₁.

## 6. lem:tower-cofinality (ordinals.tex 612): class X, with a small conditional core

Statement: sup_n ψ_B(a_n) = ψ_B(Λ) = BH, where a_{n+1} = Ω^{a_n} and Λ = ε_{Ω+1}. Proof: from (P) and
|a_n| ≤ 1 < ψ_B(a_m), the values are strictly increasing, so their sup is N_B-critical. It satisfies (P)'s
endpoint clause through a common cofinal index. Leastness gives ≤, and (P) at Λ gives ≥. "ψ_B(Λ) = BH" is cited from Pohlers
§§9.4–9.5.

- Not found: ψ_B, the coefficient norm |·|, N_B-criticality, characterization (P) (Simmons 2004 §5), and the identification
  ψ_B(ε_{Ω+1}) = BH. `NATIVE-TOWER-DEPENDENCIES.md` lists these as absent. It also says the exact Simmons 2004 §5 definitions
  and hypotheses "still need" to be obtained; only the publisher abstract was consulted.
- Small piece available: the displayed argument, taking (P), criticality closure under countable increasing sups, and the norm
  bound as hypotheses on an abstract ψ, is a short ordinal argument (class N, small). It would not make the label checked
  without the two external results.

## 7. thm:height (ordinals.tex 634): classes X + I + N (dependent)

Statement: the descending height of ⊐ is BH, cofinally witnessed by closed native terms of type o→o. Proof: (R) r_σ(t_n) ≥
ψ_B(a_n), plus tower cofinality for the lower bound, plus thm:upper.

- (R) chain: zero, successor and ω realizers (§ before (B)). add/mul/one/pow/fix/Next: #518 generic assembly over all nine
  operators. Literal native reductions: #512, plus `NativeOrdinalArithmetic*`/`Exponential*` drafts. The extractors (B)/(B_T)
  need thm:iteration and the abstraction rule. Their native realizers are drafted, not gated.
- Calibration Δ_n = ψ_B(a_n): Simmons 2004 Defs 2.10–2.14 and Thm 6.1/Cor 6.2, Simmons 2008 Thm 5.10 (helpfulness of every B_l),
  the identity after Lemma 6.6 (ε_B = Γ_0), and tameness (coefficient norms ≤ 1 < Γ_0). **Not found** formally: no helpfulness
  classes, no Veblen-hull collapse, no norm (dependencies note).
- Needs §6 and the second conjunct of §5. Not tractable before both external layers exist or are admitted as citations.

## 8. thm:main (paper.tex 96): class A of the other items

Items 1–5 map by label to checked statements: decidability `thm:decide` #416; preorder, strict well-founded and compatibility
via `thm:stable` #178, `thm:composition` #145 and #489; contexts and substitution `lem:structural-stability` #165; reductions
strict `thm:orient` #193; MPO `thm:rpo` #406. This mapping is by label only. I did not re-verify that each target's content
matches the item. Item 6 is thm:upper (second conjunct) plus thm:height. So thm:main is last by construction: a conjunction
alias once §5 and §7 are done.

## 9. Infrastructure measurements (realization / iteration and the rank wrapper)

(a) **Module-system twins of the legacy native closure.** `import_graph.py closure` counts:

| module | local closure | legacy | module-system |
|---|---|---|---|
| NativeOrdinalRealizationTargets | 50 | 48 | 2 |
| NativeOrdinalRealizationProof | 536 | 534 | 2 |
| NativeOrdinalIterationTargets | 140 | 138 | 2 |
| NativeOrdinalIterationProof | 660 | 653 | 7 |
| NativeClosedStrictWellFoundedChecks | 432 | 432 | 0 |
| NativeClosedBetaChecks / ApplicationChecks | 147 / 129 | all | 0 |
| NativeIteratorStrictTargets | 22 | 22 | 0 |

Within the iteration proof closure, the 653 legacy files total 32,348 lines (median 45, max 179). None imports Mathlib directly,
and all are core-only apart from the four Native-ordinal files. A header-only conversion looks mechanical, following the
precedent `MAIN-MODULE-MIGRATION.json`: 9 files, `module` / `public import` / `@[expose] public section`, non-header body hash
recorded, `logical_body_unchanged: true`. Exceptions: 129 files contain `private` declarations (242 theorems, 40 defs, 3
abbrevs, 1 structure). A heuristic grep finds **5 files** where a private def or abbrev appears in a public declaration header
(`NumberedWindowExternalWindowSubstitutionRawProof`, `…PreservationRawProof`, `…RealizationWindowProof`,
`…SourceInventoryProof`, `…TraceTypingProof`). The module system should reject those, so each needs a one-word body edit. This
is unverified: no gate was run. There are also 2 `instance` files and 1 `macro` file.

Two ways to do it, each with a cost:
- *In place* (owner only, since these files are tracked). The conversion is safe bottom-up, because a legacy file may import a
  module-system file (the realization Targets already does). But it changes the sha256 of hundreds of tracked sources that
  accepted records pin.
- *Twins* (lane-permissible). 534 or 653 new files under new paths, with every import line rewritten. Namespaces can stay,
  provided no root ever imports both copies.

Not measured: whether a module root over the 140- or 660-module twin closure plus `Mathlib.SetTheory.Ordinal.Rank` fits 1536
MiB. Evidence for it: #427's alias is a module root with 1,229 local modules (1,223 of them Mathlib-dependent) that passed one
native run. That run was a cloud gate, and its evidence file records no cap. My round-1/2 module roots over Mathlib `Computable`
passed locally.

(b) **Register-level conjunction, precedent #427.** #427 is *not* a register-level gluing. Its single exact alias
`CurrentDecisionNumberedStatementChecks.exact_current_decision_equivalence` proves the conjunction of four Full contracts inside
one Lean file, in one native run (receipt `1795075611944895869-2`). The earlier subgate #426 is explicitly limited: "not
whole-run pass … remain separately gated". So the precedent supports one combined gate, not separate gates joined in the
register. For Paper 16 a gluing is also ill-typed. The generic theorem quantifies over `TermStructure` and `wf`. Instantiating
it at `nativeTerms S` with `WellFounded NativeBelow` *is* the step that needs both import closures in one file. Only an owner
decision to accept a human modus ponens across two gates would make (b) usable. It would unblock realization (a)–(c), and
iteration given that. It does nothing for (d)'s general reading, §4–§7, or the rank wrapper in §5.

## 10. Ranking by tractability

1. **lem:structural-interpretation**: no new Lean mathematics. A conjunction of #394/#396/#397/#398 once the owner amends the
   clause to fixed points (owner action, not lane work).
2. **thm:iteration**: every mathematical piece is checked. Missing only the native specialization behind the import boundary
   (§9a), and it does not need the contested lambda clause.
3. **lem:realization**: the same infrastructure, plus an owner reading of "typed lambda fundamental lemma". It is assembly if it
   means the abstraction rule the printed proof proves; new mathematics if the general lemma is meant.
4. **lem:arithmetic-accessibility**: purely internal, no external literature. But 6–7 of its 9 internal components have no
   counterpart, and the nearest (forward matching) is still open.
5. **lem:tower-cofinality**: a short conditional core, but ψ_B, (P) and the BH identification are unformalized external results.
6. **thm:upper**: well-foundedness is done (#489) and rank domination is gated on the twins (22 Nov update). The bound still
   needs the parked rank = I-norm drafts (§5 step 1), §4, and an ordinal analysis of ID₁ (Pohlers).
7. **thm:height**: everything in 2, 3, 5 and 6, plus the Simmons calibration.
8. **thm:main**: a conjunction including 6 and 7.

**Single most valuable next proof-lane task:** a gate-measured pilot of §9a. Convert the 22-module `NativeIteratorStrictTargets`
closure, then the 140-module `NativeOrdinalIterationTargets` closure, to module-system twins. Record peak RSS against 1536 MiB,
then gate the iteration specialization. If it fits, thm:iteration and lem:realization (a)–(c) become assembly, and the same
method applies to the `NativeRankOrder` wrapper of thm:upper. Before starting, the owner must choose between twins and an
in-place migration, which changes accepted pins.
