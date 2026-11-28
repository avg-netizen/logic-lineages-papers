# `TypedCarrierComputability` on the front window — status map

Fable B3, 27 November 2026. Written before any Lean run of this session; the "gated this
session" column is filled in afterwards from `LEDGER.md` (append-only notes at the end).

**What "read" means below.** Every Lean name was read in its file this session as a
*statement* (and, where short, as a proof). Nothing here was re-run except where a receipt
is given. Where I rely on a file name or a handoff sentence rather than on a statement I
read, the row says "per handoff" or "by name only".

Paths: `PM/` = `LogicLineages/PersistentMarking/`, `NM/` =
`LogicLineages/NativeModule/PersistentMarking/`, `P16…` = `Paper16AccessibilityMilestone…`,
`NWIL…` = `NumberedWindowInternalLiteral…`, `NWI…` = `NumberedWindowInternal…`.

## 0. The setting

**Window.** `P16…FrontTypingProofV2.exact_FrontLiteralWindowTyping` (receipt
`1795815925311427086-1102198`): for every closed `K` an `A : InstalledWindow S K (sourceWindow K)`
and programs `H seed V₀ leaves other base₀ T baseM₀ L₀ X` with, for every `c`:

- equations `A.raw = guardedRaw (strictDualRaw C s leaf (lambdaFallback other) base base Tg Va Tg)`,
  `A.scalar = finiteScalar (addressScalar cv tv (joinedAuxiliaryWindow …) A.least) (finiteCodes W)`,
  `A.application = applicationCore A.least`,
  `A.probes.applicationGuard = applicationGuard A.scalar A.least`,
  `A.least = memoFilteredLeast C (joinedBiAuxBase …) s`; `MemoSelectedReports`, `OpenRankTypeGuards`;
- `rules : BetaJoinedRulesAt A.presentation A.scalar p h L₀ A.least U W A.probes c`
  (`PM/NWILConcreteBetaJoinedRulesProof`), with `p := applicationGuard A.scalar A.least`,
  `h := installedHop A` (`P16…BetaAddressProof`), `U := zeroDepthInstance (singletonLambda Va shift (singletonBound Va shift seed))`;
- `FreshAddressCarrier`, `FreshSeedLeast`, `CarrierTypingCases A c`,
  `TypedCarrierComputability A c → AllTerms A c`.

**Goal.** `TypedCarrierComputability A c` (`P16…TargetsV2`): for `τ ∈ K`, from
`⊢ carrier(q)` and `⊢ typedAt (chosenH A.probes W) (formulaType τ) q` derive
`⊢ formula A.probes.applicationGuard (formulaType τ) q`, in every context `Γ`, over
`sourceBody A.presentation c`. Write `C_τ(q)` for `formula p τ q`
(`PM/NumberedWindowComputabilityFormulaTargets`): `C_o(q) = I(q)`,
`C_{σ→τ}(q) = ∀u v (accepts p q u v → C_σ(u) → C_τ(v))`.

**Addresses.** A scalar address is `addressTerm ctx ty k`
(`PM/NWIFreshProbeParsedEmitterObjectTargets`): packed de Bruijn binder context, type code,
and the *least representative* `k` of its class (`programGraph A.least (suc k) ![ctx,ty,k]`).
Raw nodes are `rawCons (numeral tag) (packedBody fields)`; tags from
`PM/NumberedWindowSyntaxAlgorithm.termParts`:

| tag | node | fields |
| --- | --- | --- |
| 0 | free variable | `[ty, name]` |
| 1 | bound variable | `[ty, index]` |
| 2 | lambda | `[binder ty, body]` (`rawLambdaTerm`) |
| 3 | bottom | `[ty]` |
| 4 | ordinary head `f(b⃗)` | `[head, bases]` |
| 5 | numbered head `f^k_τ(b⃗;e⃗)` | `[head, ty, label, bases, extras]` |
| 6 | auxiliary application `QU` | `[dom, cod, fn, arg]` (`auxiliaryTerm`) |

**Recognizers already in use.** `freeSource = atomSource 0 2`, `bottomSource = atomSource 3 1`
(`PM/NWIAtomicRefinementDefinitions`), `neutralSource = addressGood ∧ header ≠ 2`
(`PM/NWILNeutralAtomProof`: every non-lambda, *including heads 4 and 5 and applications*),
`rawLambdaShape = nodeGood 2 2` (`PM/NWILBetaLeafProof`).

**One-hop relation.** `direct data h c x y` (`PM/NWINeutralFactsTargets`) is the one-step raw
reduction checked by `h`; `edge data false c x y` is `R_S` (nonempty positive path, checker
`A.path = addressPositive cv tv R A.least`). `rules.arithmetic.pathFirstHop` splits an edge into a
first hop and a remainder.

**Raw rules.** A direct certificate carries a rule tag
(`PM/NumberedWindowRootDispatchAlgorithm.parts`): 0 mark, 1 lower, 2 select, 3 copy,
4 stat (multiset replacement), 5 fabs (abstraction creation), 6 beta, 7 bottom; or it is a
contextual step (lambda body, head argument, function side of an application).
`PM/NWILDirectRuleCasesProof.exact_OpenLiteralDirectRuleCases` exposes the tag, the payload and
`bit (leaf tag) ![source, payload, target]`. On this window `leaf = withBetaLeaf Va U leaves`:
tag 6 is the visible `literalBetaLeaf Va U`; **tags 0–5 and 7 are `leaves tag`, an existential
witness with numeric calibration only.** Contextual steps go through `lambdaFallback other`
(`other` likewise a witness).

**Opaque witnesses on this window** (the names bound by the existential of
`FrontLiteralWindowTyping`; "visible front" = what earlier sessions already put in front):

| witness | role | visible front already installed |
| --- | --- | --- |
| `V₀ : Program 1` | raw syntax leaf | `variableFrontSyntax` (tag 0), `unitAuxSyntax` (tag 6 rows) |
| `base₀ : Program 2` | strict window leaf | `variableFrontWindow` (tag 0); aux rows by `strictAuxWindow` |
| `baseM₀ : Program 1` | measure leaf | `namedMeasureBase` (named leaves) |
| `T : Program 1` | type leaf | `selectedBiAuxType` (aux rows), `OpenRankTypeGuards` |
| `leaves : Nat → Program 3` | root rule checkers | tag 6 only (`withBetaLeaf`) |
| `other : Program 3` | contextual raw cases | lambda frame only (`lambdaFallback`) |
| `H : Program 2`, `seed : Program 3` | shift / depth-instance (substitution) | lambda and bound rows (`singletonLambda`, `singletonBound`, `shiftHitLiterals`) |
| `X : Program 2` | exchange leaf | — |

Atomic *sources* are additionally front-tested in the raw checker:
`guardedRaw` (`PM/NWILAtomicRawGuardProof`) decides free (tag 0) and bottom (tag 3) sources
before calling the inner checker. That is why `variableStep` and `bottomNoStep` are theorems.

## 1. Rows

Status: **P** proved and usable on this window as it stands; **T** proved elsewhere,
transferable (what transfers is stated); **O** open. Obstacle for O rows: **(a)** unwritten
derivation over visible code, **(b)** opaque program witness (named), **(c)** missing
induction principle / induction scaffold.

### Logical layer (independent of the window's code)

| # | Printed component | Internal statement | Status |
| --- | --- | --- | --- |
| L1 | (T) arrow introduction / elimination | `PM/NumberedWindowTypeApplicationRuleChecks.exact_ApplicationIntroduction`, `exact_ApplicationElimination` (any body, any `p`) | **P** |
| L2 | "induct on I" | `ID1Completion/InternalSliceInductionProof.actualInternalSliceInduction`, `InternalSliceInductionSyntaxProof.sliceReplacement`; `membershipIntroduction` (`…/InverseApplicationProof`) | **P** |
| L3 | natural induction | `Derivation.arithmetic (.induction θ)`, `ActualInternalNaturalInduction` (`ID1Completion/InternalCalculusTargets`), supplier `natInduction` (BRIEF house style; not opened this session) | **P** (plain induction only; no course-of-values form found) |
| L4 | renaming / substitution of the formula families | `PM/NWINeutralFactsSyntaxProof` (`formulaRename`, `reductsRename`, `reductsIntro`, `atomRename`), `NWIPullbackSyntaxProof.acceptsRename`, `ID1Completion/InternalComputabilityDownwardSyntaxProof.edgeRename`, `NWIFreshProbeDispatchWitnessSyntaxProof.typedRename`, `renameInto` | **P** |

### Computability facts (the paper's "joint induction on type")

| # | Printed component | Internal statement on this window | Status |
| --- | --- | --- | --- |
| N1 | neutral lemma: a non-lambda whose direct reducts are computable is computable | `FactsAt.neutral`: `carrier x`, `atom neutralSource x`, `reducts data p h c τ x ⊢ C_τ(x)`; `PM/NWINeutralFactsProof.exact_ConditionalInternalNeutralFacts rules.arithmetic τ` | **P** (instantiation; frozen this session as `WindowNeutralFacts`; gate status in §3) |
| N2 | bottoms computable | `FactsAt.bottom`: `carrier x`, `atom bottomSource x ⊢ C_τ(x)` | **P** (same theorem) |
| N3 | free variables computable | `FactsAt.variableCase`: `carrier x`, `atom freeSource x ⊢ C_τ(x)`; the *selected fresh* ones also by `rules.fresh : FreshVariablesComputable` | **P** (same theorem) |
| N4 | bound variables (tag 1) computable | needs `atom neutralSource x` from header 1 (`neutralFromHeader`, (a), small) and **`BoundStep`**: `nodeGood 1 2` source, `direct x y ⊢ atom bottomSource y` (the tag-1 analogue of `Arithmetic.variableStep`) | **O (b)**: the step law for tag 0 exists only because `guardedRaw` front-tests tag-0 sources; for tag 1 the inner checker's rule leaves `leaves 0…5,7` and `other` decide. Repair by the round's pattern: extend `guardedRaw` with a tag-1 front (`nodeGood 1 2` ⇒ target must be `exactRawBottom`), calibration preserved because numerically a bound variable has only the bottom step; then re-select the packet (A.raw changes, so `FrontPacketV2`/`FrontRulesV2`/`FrontWindowProofV2` are regenerated) |
| N5 | applications are neutral; reducts of `x u` for non-lambda `x` are bottom or inherited | `rules.applicationOutput : ApplicationOutput` (carrier and `atom neutralSource` of every accepted result), `rules.inversion : InstalledNeutralInversion`, packaged in `rules.arithmetic.applicationNeutral/applicationInversion` | **P** |
| N6 | computability ⇒ I | `rules.typedComputableToMember`: `typedAt τ q`, `C_τ(q) ⊢ I(q)` (via `rules.pullback`, `rules.fresh`, typed probe of the installed tuple) | **P** |
| N7 | preservation by `R_S` (downward closure) | `PM/NWIDownwardChecks.exact_ComputabilityDownward`, conditional on `ApplicationEdgeMatching data p c` (round-6 **M1**) | **O (a)**, with a correction to the frozen statement. *Finding of this session:* `ApplicationEdgeMatching` has no carrier premise on the edge's source `f`, and on this window an edge does not entail the scalar of its source (`addressPositive` checks only the address shell and the two guards at each end; `rawWithTarget`'s `targetGate` calls the scalar on the target only), while the conclusion `accepts p f u w` needs `unary i (suc z) f`. So M1 as frozen is not derivable by composition (possibly false at non-carrier sources; not checked numerically). The derivable statement is **`CarrierMatching`**: `carrier f`, `edge f g`, `accepts p g u v ⊢ ∃w (accepts p f u w ∧ edge w v)`, and downward closure with the same extra premise (enough for every use in the printed proof; the recursion stays inside carriers by `rules.applicationOutput`). Its derivation is a composition of existing laws: open the edge (`NWILPositiveCertificateRowsProof.exact_OpenLiteralPositiveCertificateRows`: both endpoints share context and type), open the acceptance at `g` (`NWILApplicationRowsProof.exact_OpenLiteralApplicationRows`), identify fields by `valueUnique` and move them by `outputTransport`, **K2 for arbitrary carriers (`GeneralSeedLeastOnJoinedWindow`, frozen this session; gate status in §3)**, rebuild the acceptance at `f` (`NWILApplicationRebuildProof.exact_OpenLiteralApplicationFromReportedLeast`), `rules.forward`, and `PM/NWISparseApplicationReinstallUniqueChecks.exact_UniqueGuardedApplication` to identify the forward image with `v`. Unwritten parts: four nested renamings (`matched` has no renaming lemma; `imageRename` of `NWILPushedForwardImageProof` is the model), and an equality transport in the second argument of `edge` (no supplier located; `edgeExists` + a transport on the certificate graph's third input is the likely route) |
| N8 | `ApplicationArithmetic A c` (frozen in `P16…TargetsV2`) | `forwardEdge` = `rules.forward`; `typedProbe` = component 9 of `A.installed.1` (as in `NWILFreshNeutralBridgeProof.exact_TupleComputabilityToIFromArithmetic`); `freshComputable` = `rules.fresh`; `matchEdge` = M1 as frozen | three fields **P**; `matchEdge` **not derivable as frozen** (N7). `exact_CloseAllTerms` does not consume it, and the reduction `TypedCarrierComputability → AllTerms` on this window does not take `ApplicationArithmetic` at all, so nothing downstream is blocked |

### Lambda fact

| # | Printed component | Internal statement | Status |
| --- | --- | --- | --- |
| B1 | reducts of `(λ.V) U`: beta instance, function-side reduct, bottom | `rules.betaCases : BetaApplicationCases` (`PM/NWILBetaApplicationComputabilityProof`): from `accepts p x u t`, `direct t y` and a continuation `BetaOutcomeAt … goal`: `atom bottom y ∨ inherited x u y ∨ goal` | **P** |
| B2 | an accepted application is computable if the function's direct reducts are computable at the arrow type, the argument is computable, and every aligned beta outcome is computable | `NWILBetaApplicationComputabilityProof.exact_OpenApplicationComputabilityFromBeta` with `rules.arithmetic`, `rules.applicationOutput`, `rules.betaCases` | **P** (instantiation; frozen this session as `WindowBetaApplication`; gate status in §3) |
| B3 | the beta outcome's target is a typed carrier | `P16…BetaAddressProof.exact_OpenInstalledBetaRebuiltAddress`, `exact_OpenInstalledBetaRebuiltComputability`, `exact_OpenInstalledBetaDirectTypeField`, `exact_OpenInstalledBetaApplicationTypeField`, `exact_OpenInstalledCarrierRequestedType`; nested-lambda body split `P16…BetaLambdaConsumerRepairCheckProof.exact_OpenInstalledAlignedBetaLambdaComputability` (import the `RepairCheck` copy). All take `CarrierTypingCases A c` (now a theorem) and `BetaJoinedRulesAt` as hypotheses | **P** as consumers. What they do *not* give: the type equation `st = code τ` at the target without either `typedAt τ t` for the application result `t` (then `…BetaDirectTypeField`) or `eqn st cod` (`BetaOutcomeWithTypeAt`, which `rules.betaCases` does not export — `NWILJoinedBetaOutcomeProof.exact_OpenJoinedBetaOutcomeWithType` needs the packet hypotheses `reverse ends stable selected guards`, not exported by the window). **Small open (a)**: `ApplicationResultTyped`: `typedAt (σ→τ) x`, `accepts p x u t ⊢ typedAt τ t` (open the acceptance with `exact_OpenLiteralApplicationRows`, read `rawResult` of `addressTerm ctx cod k` by `literalAddress`, `actualArrowFields` for `cod = code τ`, then `exact_OpenInstalledCarrierRequestedType` with `rules.applicationOutput` for the carrier) |
| B4 | identity body `(λ.0) U ⇝ U` | `PM/NWILBetaIdentityProof`, `NWILBetaIdentityTypingProof`, `NWILBetaIdentityConsumerProof.exact_OpenAlignedIdentityBetaFromHop` (receipt `1795740901799185973-10`, per handoff) | **P** for that one body shape; needs the physical hop and `sc = ctx` in scope, which `BetaOutcomeAt` does not pass (per handoff) |
| B5 | "substituting a fresh variable first gives I(V)"; here: `I(x)` for a lambda address `x` whose instances are computable | apply `x` to its selected fresh address (`TypedProbeTotal`: `witnesses p h a τ q`), B2 with `u` fresh and N3, then N6. Needs B6 for the function-side reducts inside B2 — circular unless done inside the I-induction of B7 | **O (a)**, no new arithmetic; part of B7's derivation |
| B6 | direct reducts of a lambda are lambdas over a body reduct, or bottom | **`LambdaStepInversion`**: `rawLambdaShape` source `x = (ctx, σ→τ, λσ.b)`, `direct x y ⊢ atom bottomSource y ∨ ∃ b' (y = (ctx, σ→τ, class of λσ.b') ∧ direct (σ::ctx, τ, b) (σ::ctx, τ, b'))` | **O (b)+(a)**. Per `codex-lambda-prefix-handoff.md`: the strict row on a lambda and the first tick of the prefix program are derived (`PM/NWILJoinedLambdaChildWindowProof.exact_OpenJoinedLambdaNonRecursiveDescent`, `NWILLambdaPrefixContextIntroProof`, `NWILLambdaPrefixParentStopProof`, `NWILLambdaPrefixHopProjectionProof`, all compiled per `root/CODEX-DRAFT-GATE-RESULTS.md`) for children with both selectors zero; "promotion for auxiliary or nested lambda children and recurrence beyond a stopped prefix child remain open", and the child window in the pushed context calls the opaque `base₀`. Excluding the root rules 0–5 at a lambda source needs `leaves` (b) or a lambda-source front in `guardedRaw` |
| B7 | lambda fact: `C(λ.V)` from `∀U (C(U) ⇒ C(V[U]))`, by induction on `I(λ.V)` retaining the instance premise | **`LambdaFact`**: for `rawLambdaShape` `x` typed `σ→τ`: `(instances of x at computable arguments are computable) ⊢ C_{σ→τ}(x)`. Derivation: L2 on `θ(x) := lambda(x) ∧ typed(x) ∧ Inst(x) → C_{σ→τ}(x)`; inside, L1-intro, B2, with function-side reducts by B6 + induction hypothesis, whose instance premise needs B8 + N7 | **O (c)+(a)**: the invariant `Inst(x)` must be an *object formula* ("for all `u, w`: `C_σ(u)` and `w` is the beta target of `x,u` ⟹ `C_τ(w)`"); the beta-target relation is expressible with the visible programs (`programGraph U`, `programGraph A.least`, `addressReport`), so no new program is needed, but the formula, its renaming lemma and the slice-induction instance are unwritten |
| B8 | substitution maps a raw step to a raw path or an equality (round-6 **M6**) | **`InstanceStep`**: `direct (σ::ctx,τ,b) (σ::ctx,τ,b')`, instance runs `U(a,b) = r`, `U(a,b') = r'` ⊢ `class(r) = class(r') ∨ edge (ctx,τ,r) (ctx,τ,r')` | **O (b)**: `U` is visible only on lambda and bound rows; on tags 0, 3, 4, 5, 6 it is `seed` (`DepthInstanceFit seed`, `PM/NWILSingletonDepthNumericProof.exact_LiteralDepthInstance`, Primrec existence) and the shift is `H` (`ShiftHitFit`). Also needs every root rule's behaviour under substitution: `leaves` (b). External template: `PM/NumberedWindowExternalInstancePathProof`, `NumberedWindowExternalRawSubstitution…` |

### Multisets and the constructor induction (L)

| # | Printed component | Internal statement | Status |
| --- | --- | --- | --- |
| J1 | J closed under union; `I(Q) ⇒ J({Q})`; accessible members ⇒ J | `P16…FinishMultisetsV2.exact_FinishMultisets` (receipt `1795773714932362718-921018`): `CertifiedMultisetUnion A c → MultisetGeneration A c u mem sg → SingletonAccessibility ∧ MembersAccessibility` | implication **P**; its two premises (`CertifiedOriginSplit`, `LiteralJUnion`; seven generation laws for selected `u mem sg`) were **not re-examined this session**; per `fableB/PLAN.md` they are open on installed windows |
| H1 | every reduct of a constructor term is produced by one of the rules, with its certificate content (round-6 **M8**) | **`HeadStepCases`**: source tag 4 or 5, `direct x y ⊢` eight-way disjunction with each rule's relation between source fields and target (mark: label ω→k; lower: k+1→k; select: `q P^k…P^k`; copy: smaller head, bases `P^k`; stat: DM-replacement of the base list by mark-decrease descendants; fabs: `λ. f^k(b⃗; e⃗, 0)`; bottom; contextual: one base or extra argument stepped) | **O (b)**: the tag and payload are exposed (`exact_OpenLiteralDirectRuleCases`), but each rule's content is `bit (leaves tag) …` on an existential witness; contextual argument steps are `other`. This is the largest opacity item: seven rule checkers and the argument-context checker need visible programs (or visible front tests strong enough to derive the rule's relation), with calibration preserved, and one more packet re-selection |
| H2 | head-class finite induction, label induction (ℕ then ω) | external recursion on the finite head-class order of `fixed S K`; L3 for labels | **O (c)**: no internal scaffold; external template `PM/NumberedWindowConstructorInductionProof.fromRaw`, `NumberedWindowConstructorOrder…`, `…ComputabilityTargets` (`Hypothesis`, `RawCases`, `OwnerComputability`) |
| H3 | (L): a constructor with computable arguments is computable | **`ConstructorFact`**: source tag 4/5 typed `τ`, all base and extra argument addresses computable at their types ⊢ `C_τ(x)`; by N1 (heads are `neutralSource`), H1, H2, J1, N7, B7 (fabs case), L1 (select case) | **O**: (b) through H1, (c) through H2; also needs **`ArgumentAddresses`** (the address of each base/extra argument of a head address is a typed carrier, and conversely the member multiset of the base list is the J-carrier the DM step acts on) — unwritten, touches `V₀`/`base₀` for head nodes (b) |

### Decoding and the outer induction

| # | Printed component | Internal statement | Status |
| --- | --- | --- | --- |
| D1 | every admitted address is a variable, lambda, bottom, head or application (round-6 **M9**, root part) | **`CarrierShapeCases`**: `carrier q ⊢ goal` from seven branches `q = addressTerm ctx ty (rawCons (numeral tag) (packedBody fields))`, tags 0–6 with their arities | **O (b)**: the header is readable (`rawHeader`, `literalHead`), and a seven-way split on it is excluded middle over `equalityTest`; but *excluding other tags and wrong arities* needs the syntax bit of the carrier's window, which for tags 1–5 is the opaque `V₀`. Repair: a visible shape front on `V₀` (reject unless tag ≤ 6 with the right arity; calibration preserved since the numeric syntax accepts nothing else), same pattern as `variableFrontSyntax` |
| D2 | subterms of an admitted term are admitted, at the right types | **`ChildAddresses`** per tag: lambda ⇒ body address in the pushed context is a typed carrier; application ⇒ D3; heads ⇒ H3's `ArgumentAddresses` | **O (b)+(a)**: window of a child from the window of its parent is the *converse* of what exists (`NWILJoinedAuxiliaryWindowProof.exact_OpenJoinedAuxiliaryParent` builds the parent from the children). For aux rows the wrappers are visible (`strictAuxWindow`, `unitAuxSyntax`), so the tag-6 case is (a); for lambda and head rows the strict window is `base₀` (b) (lambda rows partly visible per the lambda-prefix handoff: "observed lambda callback", not installed on this window) |
| D3 | an application address is the result of an accepted application | **`ApplicationDecoding`**: tag-6 carrier `t` typed `τ` ⊢ `∃ σ∈K ∃x u (accepts p x u t ∧ carrier x ∧ typedAt (σ→τ) x ∧ carrier u ∧ typedAt σ u)` | **O (a)** over visible code, two parts: (i) D2 for aux rows; (ii) class coherence: the least of `aux(dom,cod,fn,arg)` at the children's *least representatives* is the least of the stored node (the application guard re-reads the least program on `auxiliaryTerm dom cod fn arg` built from the two addresses' least fields). Suppliers to try: `CanReverse`/`WindowEndpoints`/`Preserves` laws used by `NWILJoinedForwardRowsProof`, `exact_OpenCanonicalChildHopAtLeast`; these are packet hypotheses, not exported by the window ⇒ another export (restatement) |
| D4 | application case of the structural induction | from D3, induction hypotheses at `x` and `u`, and L1-elim | **P** given D3 and the induction |
| S1 | "structural induction under a computable substitution" | **`SubstitutionInduction`**: for every raw `q` admitted at `(ctx, τ)` and every stack of computable arguments for `ctx`, the iterated instance is computable | **O (c)+(a)+(b)**. (c): needs course-of-values induction on the raw code (children of a least representative are numerically smaller, but instances are not: the induction is on the *uninstantiated* term with the substitution universally quantified inside the invariant), and an object-language representation of the argument stack with "each entry computable at its binder type" (a finite disjunction over `K` per entry, bounded quantifier over the stack). (a): an iterated-instance relation built from `programGraph U` at increasing depth, or a simultaneous substitution program, with one shape law per tag (substitution commutes with each node former). (b): those shape laws for tags 0, 3, 4, 5, 6 are again `seed`/`H`. External template: `PM/NumberedWindowStructuralComputabilityTargets.StructuralComputableSubstitution` (`Environment`, `substitute values 0 q`), `NumberedWindowStructuralEnvironmentProof`, `NumberedWindowStructuralLambdaProof` |

## 2. How the rows compose

`TypedCarrierComputability A c` = S1 at the empty stack. S1's induction step, by D1:

- tag 0: N3 (stack does not touch free names).
- tag 1: the stack entry (computable by hypothesis) or, above the stack, N4.
- tag 3: N2.
- tag 6: D3, hypotheses, L1 (D4), with the substitution shape law.
- tag 2: B7, whose instance premise is the induction hypothesis for the body with the stack
  extended by one computable argument.
- tags 4, 5: H3 with hypotheses for the arguments.

B7 uses B2, B3, B5, B6, B8, N7, N6, L2. H3 uses N1, H1, H2, J1, N7, B7, L1.

**Closed before this session:** L1–L4, N1–N3, N5, N6, B1, B2 (as general theorems needing only
instantiation), B3 consumers, B4, J1's implication.
**Closable by composition (no new arithmetic):** N7 in its carrier-relativized form `CarrierMatching` (totality half frozen this session; gate status in §3), B3's `ApplicationResultTyped`.
**Blocked on opaque witnesses (b):** N4 (`leaves`, `other` → raw guard), B6 (`leaves`, `base₀`),
B8 (`seed`, `H`, `leaves`), H1 (`leaves`, `other`), D1 (`V₀`), D2 (`base₀`, `V₀`), S1's shape
laws (`seed`, `H`).
**Blocked on scaffolding (c):** B7's object-formula invariant, H2, S1.

The recurring repair (visible front tests with all-input calibration preserved, then a packet
re-selection) would have to be applied, in one re-selection if possible, to: `V₀` (shape front,
D1), `guardedRaw` (tag-1 and lambda sources, N4/B6), `leaves 0…5,7` and `other` (H1 — these need
the rules' *content*, so front tests are not enough: explicit rule programs), `seed`/`H`
(explicit substitution on every tag). The last two are the round-6 design recommendation
("replace the presentation programs by explicit program definitions") restricted to the raw
rule checkers and the substitution program.

## 3. What this session froze and gated

See `LEDGER.md` for receipts; this section is appended after each gate.

### 3.1 The closing split frozen this session (status as of 20:30, before any gate verdict)

Frozen in `NM/P16…TypedRowsTargetsV2` (all statements about an arbitrary installed window with
`JoinedAt A L₀ U c`, i.e. the `BetaJoinedRulesAt` package at its own programs):

`TypedComputabilityFromRows`: guard equation, `JoinedAt`, and the four rows below
⟹ `TypedCarrierComputability A c`. Proof (in `…TypedRowsProofV2`): excluded middle on
`atom neutralSource q`; neutral branch = N1 applied to `NeutralReducts`; other branch = case on
the source type, ground by `GroundNotLambda`, arrow by `LambdaFactFromReducts` (L1-intro + B2).

| Open row (Lean name) | Says | Contains map rows | Obstacle |
| --- | --- | --- | --- |
| `NeutralReducts A c` | every direct reduct of a typed non-lambda carrier is computable at its type | N4 (bound variables), D1–D4 (decoding, applications), H1–H3 with J1 (constructors), and their use in S1; free variables and bottoms are already covered inside it by N2/N3 with `variableStep`/`bottomNoStep` | (b) `leaves`, `other`, `V₀`, `base₀`; (c) H2, S1 |
| `GroundNotLambda A c` | a carrier typed at the ground type passes the neutral test | new small row: a lambda node admitted at a non-arrow type code is impossible | (b) `base₀`: the strict window at a lambda row is the opaque leaf; with the "observed lambda callback" of the lambda-prefix handoff (parent arrow equation) it becomes (a) |
| `LambdaReducts A L₀ U c` | the direct reducts of a typed lambda carrier whose instances are computable are computable at the arrow type | B5, B6, B8, with N7 (`CarrierMatching`) and N6 | (b) `leaves`, `base₀`, `seed`, `H`; (c) the object-formula invariant of B7 |
| `LambdaInstances A L₀ U c` | every aligned beta outcome of a typed lambda carrier at a computable argument is computable | S1 (the induction hypothesis at the instance), with B3 | (c)+(a)+(b) as S1 |

The four rows are **not independent statements of increasing strength**: `NeutralReducts` and
`LambdaInstances` both contain the structural induction S1 (the paper proves them in one
induction). The split is exact and compiled-checkable, but it is a decomposition of the
*conclusion*, not of the induction. The induction itself has no internal statement yet
(S1 row above).

Also frozen: `GeneralSeedLeastOnJoinedWindow` (`NM/P16…GeneralSeedLeastTargetsV2`, K2 for
arbitrary carriers), `ApplicationResultTyped` (`NM/P16…ApplicationResultTargetsV2`, B3's small
item), and the selection `FrontLiteralWindowRows` (`NM/P16…FrontRowsTargetsV2`):
`FrontLiteralWindowTyping` with `GeneralSeedLeast A c` and
"four rows ⟹ `AllTerms A c`" attached on the same window.

Gate verdicts for all of the above: see `LEDGER.md` (appended there as they arrive) and §3.2
below if present.

### Caveats on what was read (appended 20:33)

- B8 / S1: that the instance program `U` is visible only on lambda and bound rows and calls
  `seed` elsewhere is taken from the definitions' names and signatures
  (`singletonLambda V H U`, `singletonLambdaDispatch`, `singletonBound V H U`,
  `singletonBoundDispatch`, `DepthInstanceFit`), not from reading the dispatch bodies. Check
  `PM/NWILSingletonLambdaMachineProof` lines 44–52 and `PM/NWILSingletonBoundMachineProof`
  lines 56–63 before building on it.
- H1: the rule-tag table is `PM/NumberedWindowRootDispatchAlgorithm.parts` (read); that the
  installed root is `root leaf` with `leaf = withBetaLeaf Va U leaves` is from
  `exact_OpenLiteralDirectRuleCases` and the window's `A.raw` equation (read); what
  `strictDualRaw` adds around the root (windows at both ends) was not opened.
- D1/D2: "the wrappers intercept only auxiliary rows" is root's finding
  (`root/K1-VARIABLE-NODE-FINDING.md`) plus B2's variable fronts; I did not re-open
  `unitAuxSyntax` or `strictAuxWindow`.
- J1: nothing about the multiset premises was re-read.
- External templates (`NumberedWindowExternal…`, `NumberedWindowConstructor…`,
  `NumberedWindowStructural…`) were opened only at their Targets modules.

### 3.2 Gate status (appended 20:53) — **EVERYTHING IN §3.1 IS UNGATED**

No module written by this session has been compiled. The compiler's 2048 MiB free-memory floor
was not met from 20:14 on (other sessions' processes; not this round's to stop). Wherever
sections 1–3.1 say a row is "frozen this session", read: *statement and proof text on disk,
never elaborated by Lean*. Rows marked **P** in section 1 with an existing theorem name
(`exact_ConditionalInternalNeutralFacts`, `exact_OpenApplicationComputabilityFromBeta`, the
`BetaAddressProof` consumers, …) are proved by those *existing, previously gated* theorems; only
their restatement on the window (`WindowNeutralFacts`, `WindowBetaApplication`) is ungated.

| Module (`NM/P16…`) | Content | Status |
| --- | --- | --- |
| `TypedRowsTargetsV2` | `WindowNeutralFacts`, `WindowBetaApplication`, `LambdaFactFromReducts`, `TypedComputabilityFromRows`; open rows `NeutralReducts`, `GroundNotLambda`, `LambdaReducts`, `LambdaInstances` | UNGATED |
| `TypedRowsProofV2` | `exact_WindowNeutralFacts`, `exact_WindowBetaApplication`, `exact_LambdaFactFromReducts`, `exact_TypedComputabilityFromRows` | UNGATED draft |
| `GeneralSeedLeastTargetsV2` | `GeneralSeedLeast`, `GeneralSeedLeastOnJoinedWindow` | UNGATED |
| `GeneralSeedLeastProofV2` | `exact_GeneralSeedLeastOnJoinedWindow` (script-generated from B2's gated `FreshSeedLeastProofV2`) | UNGATED draft |
| `ApplicationResultTargetsV2` | `ApplicationResultTyped` | UNGATED |
| `ApplicationResultProofV2` | `exact_ApplicationResultTyped` | UNGATED draft |
| `FrontRowsTargetsV2` | `FrontLiteralWindowRows` | UNGATED |
| `FrontRowsProofV2` | `exact_FrontLiteralWindowRows` | UNGATED draft |

If a later entry in `LEDGER.md` records a passing receipt for one of these, that entry
supersedes this table for that module.

Gate order for whoever resumes (each call from ROOT,
`bash verification/local-fable-trio-2026-11-27/gate.sh mathlib …`):
1. `…TypedRowsTargetsV2 …TypedRowsProofV2`
2. `…GeneralSeedLeastTargetsV2 …GeneralSeedLeastProofV2 …FrontRowsTargetsV2 …FrontRowsProofV2`
   (FrontRows depends on 1 and on GeneralSeedLeast)
3. `…ApplicationResultTargetsV2 …ApplicationResultProofV2` (independent of 2; depends on 1's
   Targets)

Most likely elaboration risks, in the order I would look: (i) `TypedRowsProofV2`, the two
`rw [e]` steps and `keepBoth` in `exact_LambdaFactFromReducts` (rewriting under the let-bound
`x'`); (ii) the `cases τ` branch of `exact_TypedComputabilityFromRows`, which relies on
`formulaType (.arrow σ ρ)` unfolding by definitional equality, as `BetaAddressProof` does;
(iii) `ApplicationResultProofV2`, the `headTransport` call (`![t]` against `Fin.cons t ![]`) and
the name resolution of `rawResult`/`literalAddress`.
