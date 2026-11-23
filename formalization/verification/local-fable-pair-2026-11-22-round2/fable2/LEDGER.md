# Fable-2 ledger

## G01 — output address

### Plan (written before the target was frozen)

1. The output address is not an address of `auxiliaryTerm dom cod fn arg` itself. The original
   frontend's `outputReport least ctx cod aux y` says `y = addressTerm ctx cod k` where `k` is the
   packed least of `aux`. So the term is `q := addressTerm ctx cod m` with `m` the measured least of
   the auxiliary term, and its report is `addressReport q ctx cod m` (class field `m`, not `aux`).
2. `m` is fresh: it comes out of `hasLeast` (integration statement, `casesLeast`), so the result is
   in continuation form over `(β) (j : α → β) (Δ) (m : OTerm β)`.
3. Report formula: `addressReport (addressTerm ctx cod m) ctx cod m` — unconditional, from
   `NumberedWindowInternalAtomicRefinementObjectSelectorsProof.literalAddress`.
4. Acceptance predicate: `unary Q.scalar (suc z) q`, via `exact_InstalledCarrierFromCoordinates`,
   which needs four coordinates at `(ctx, cod, m)`:
   - `unary cv (suc z) ctx` — from `exact_InstalledCarrierCoordinates` on the function address;
   - `windowAt Q.window ctx cod m` — `exact_OpenCoverCombinedWrappedAuxFormation` gives the window
     at `aux`; `exact_SelectedWindowFromRetained exact_RetainedPredecessor` moves it to the least;
   - `leastGraph … ctx cod m m` (the fixed point) — `exact_CoveredLeastIdempotent`, applicable
     because `thinPairedExchange`/`thinMatchingWindow` are literal recuts of
     `pairedExchange`/`coveredWindow` (expected definitional; the gate decides);
   - `unary tv (suc z) cod` — NOT derivable: `tv` is an arbitrary program and the operands only give
     `tv (rawCons dom cod)` and `tv dom`. It is also necessary (Coordinates applied to the conclusion
     returns it). Kept as one explicit result-type guard.
5. Second statement: at `tv := TV` that guard is the right half of the retained syntax guard, so
   only the two original type guards remain.
6. Not attempted: packaging into `programGraph Q.application (suc z) ![qf,qa,q]` (needs
   `arrowGood qf`, `arrowReports`, the two shell equations and a six-witness block).

### Targets (frozen before proof authoring)

- `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationOutputAddressTargets.lean`
  sha256 `7164f6998e96658f10e0a5e55b9cfbb821de9655aef7262e0254b521afaf8eca` (2026-11-23T01:21Z)
  - `ExactInstalledApplicationOutputAddress`
  - `ExactInstalledSyntaxGuardedApplicationOutputAddress`

### Receipts

- 2026-11-23T01:28Z — gate `mathlib …OutputAddressProof`, attempt 1 of 1: `COMPILE_PASS` for
  Targets and Proof. Receipt `build-reports/1795397242217822492-3231382.json`
  (sha256 `6f255001348057c2d37b2a6b31ba867356dd46cfdcad7655397028b8e47d5c3d`).
  Proof module sha256 `492c77121cf8bd9f02361f4b45ec8788db06636382e7b0b4bf7cc2f4797519ab`.
  Targets sha256 re-checked after the pass: unchanged.
  `#print axioms`: both theorems `[propext, Classical.choice, Quot.sound]`.

### Failures

None. The one open expectation in the plan (that `thinPairedExchange` / `thinMatchingWindow` unfold
to `pairedExchange` / `coveredWindow` so the accepted idempotence applies) held in the kernel.

### State and next

PASSED. `exact_InstalledApplicationOutputAddress` and
`exact_InstalledSyntaxGuardedApplicationOutputAddress` are gated. Evidence in
`OUTPUT-ADDRESS-EVIDENCE.json`, scope in `OUTPUT-ADDRESS-SOURCE-MAP.md`.

Still explicit: the two original type guards; in the general statement also `unary tv (suc z) cod`
(necessary, not derivable for arbitrary `tv`; gone at `tv := TV`).

Next: frontend acceptance `programGraph Q.application (suc z) ![qf,qa,addressTerm ctx cod m]` via
`exact_InstalledApplicationReport`. Missing inputs to state exactly: `unary arrowGood (suc z) qf`,
`arrowReports qf dom cod`, and the shell equations for `qf`, `qa` (recoverable from
`ExactOpenAddressArrowCoordinates`), then a six-witness `block` introduction around
`outputReport Q.least ctx cod aux q` — the last conjunct is exactly what this step's continuation
supplies (`leastGraph` is `programGraph Q.least (suc m) ![ctx,cod,aux]` by definition).

## G02 — frontend acceptance

### Plan (written before the proof was drafted)

Goal: `programGraph Q.application (suc z) ![qf,qa,addressTerm ctx cod m]` for the same fresh `m` as
G01, in continuation form, through the backward half of `exact_InstalledApplicationReport`.
`applicationReport i least f u y = unary i 1 f ⊓ (unary i 1 u ⊓ block (applicationRow least f u y))`,
and the row is `parsedApplicationInputs f u ctx result dom cod fn arg ⊓ outputReport …`.

Grep check of the four ingredients (each against an accepted supplier):

1. `unary arrowGood (suc z) qf` — DERIVABLE. `arrowGood = applyUnary cellGood rawResult`; the function
   report gives `unary rawResult (rawCons dom cod) qf`; `canonicalCell dom cod`
   (`…SparsePathEnvelopeOpenCellProof`) gives `cellGood` of `rawCons dom cod`; `makeUnary`
   (`…SparsePathEnvelopeOpenSyntaxProof`) composes them.
2. `arrowReports qf dom cod` — DERIVABLE the same way (`rawDomain`/`rawCodomain` are
   `applyUnary cellHead/cellTail rawResult`; `canonicalCell` gives head `dom`, tail `cod`).
3. Shell equation `qf = addressTerm ctx result fn` and `result = rawCons dom cod` — DERIVABLE:
   `assembleInputs` (`…SparseApplicationFrontendOpenShapeProof`, public) produces the whole
   `parsedApplicationInputs` from the two `addressGood`s, `arrowGood`, the two `addressReports` and
   `arrowReports`, via `exact_OpenAddressArrowCoordinates`.
4. Shell equation `qa = addressTerm ctx dom arg` — DERIVABLE, same `assembleInputs` (its private
   `argumentEquation` uses `readNode`).

`addressGood` and `addressReports` for both operands are the literal conjuncts of `addressReport`.
Six-witness `block` introduction: accepted supplier exists — `supply`
(`…SparseApplicationFrontendOpenBindingProof`, public); no private lemma needed.
`outputReport` introduction: `reportUnfold` + `Derivation.existentialIntroduction (emb m)` +
`reportInstance` (`…SparseApplicationOutputCoreReportSyntaxProof`), with the G01 least call and
`refl` for the address equation.

So NO new hypothesis is expected: the target has exactly the G01 premises and adds one conjunct
(the application graph) to the continuation. Inputs are assembled in `Γ`, then moved to `Δ` with
`renameInto` + `inputsRename`; witness for `result` is `(rawCons dom cod).relabel j` left unrewritten.
Open expectations for the gate: (a) `Q.least` unifies with `packedLeastProgram Q.source.cover
Q.exchange Q.window s` (projection of `install`); (b) `unary`/`applyUnary` definitional unfolding
suffices for `arrowGood`/`arrowReports`/`addressReports` without rewriting.

### Targets (frozen before proof authoring)

- `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceTargets.lean`
  sha256 `05b5b51e5d35074f926ea1517f316495a714aff5a0783388b028529993fd3a64` (2026-11-23T01:33Z)
  - `ExactInstalledApplicationFrontendAcceptance`
  - `ExactInstalledSyntaxGuardedApplicationFrontendAcceptance`

### Receipts

- 2026-11-23T01:34Z — gate `mathlib …FrontendAcceptanceProof`, attempt 1 of 1: `COMPILE_PASS` for
  Targets and Proof. Receipt `build-reports/1795397653724718198-3233856.json`
  (sha256 `e8421c35fbec3e3af59a85f4f146fc8fbc9b3f7cb69b75fa32e3e34af0a81999`).
  Proof module sha256 `904d8faf4fcf9213711fd38a73583b6cc8a6d18b8a46018ffd73b179f601dfee`.
  Targets sha256 re-checked after the pass: unchanged.
  `#print axioms`: both theorems `[propext, Classical.choice, Quot.sound]`.

### Failures

None. Both open expectations held: `Q.least` unified with the `packedLeastProgram` inside
`leastGraph`, and `arrowGood` / `arrowReports` / `addressReports` needed no rewriting.

### State and next

PASSED. `exact_InstalledApplicationFrontendAcceptance` and
`exact_InstalledSyntaxGuardedApplicationFrontendAcceptance` are gated. Evidence in
`FRONTEND-ACCEPTANCE-EVIDENCE.json`, scope in `FRONTEND-ACCEPTANCE-SOURCE-MAP.md`.

All four handoff ingredients (`arrowGood qf`, `arrowReports qf dom cod`, both shell equations) were
derived from the two operand `addressReport`s; the block came from the accepted `supply`. No
premise was added to G01's. Private glue in the proof module: `parsedFromReports`,
`outputFromLeast`.

Still explicit (inherited): the two original type guards; in the general statement
`unary tv (suc z) cod`. Observation for whoever states the next step: the application-graph
conjunct alone does not use the `tv` guard — only G01's scalar-acceptance conjunct does.

Next: closure of the installed carrier under application as one statement — the set
`{q | unary Q.scalar 1 q}` with reports is closed under the installed application program
(existence, done here; plus functionality: any `y` with `programGraph Q.application 1 ![qf,qa,y]`
equals the emitted address). Candidate route, UNCHECKED: forward half of
`exact_InstalledApplicationReport`, identify its fresh block witnesses with `ctx, dom, cod, fn, arg`
through the shell equations, then `coherent` in `…SparseApplicationReinstallReportCasesProof`.
After that, the two type guards: at `tv := TV` operand acceptance gives `TV (rawCons dom cod)` and
`TV dom`; whether an accepted arrow-inversion law for `TV` / the refit guard exists was not
grepped.

## G03 — output functionality

### Plan (written before the proof was drafted)

Goal: any `y` with `programGraph Q.application (suc z) ![qf,qa,y]` equals `addressTerm ctx cod m`
for the measured least `m` of `auxiliaryTerm dom cod fn arg`.

Route checked by reading/grep (each step against an accepted public supplier):

1. Forward half of `exact_InstalledApplicationReport` gives `applicationReport Q.scalar Q.least qf qa y`;
   its third conjunct is `someRow Q.least qf qa y`. `rowCases`
   (`…SparseApplicationFrontendOpenBindingProof`, public) opens the six-witness block to fresh
   `c r d e l a` with `parsedApplicationInputs qf qa c r d e l a ⊓ outputReport least c e (aux d e l a) y`.
2. Identify the fresh witnesses with the user's coordinates by `valueUnique` on the field programs:
   `rawContext` (`ctx = c`), `rawLeast` on `qf` (`fn = l`) and on `qa` (`arg = a`), `rawDomain`
   (`dom = d`), `rawCodomain` (`cod = e`). The user-side `rawDomain`/`rawCodomain` facts come from
   `canonicalCell` + `makeUnary`, as in G02. `r` is not needed.
3. Term congruence. NOT accepted under any name: grep for
   `eqn (rawCons …) (rawCons …)` / `eqn (auxiliaryTerm …) (auxiliaryTerm …)` finds only the private
   one-argument `addressEqual` in `…SparseApplicationReinstallResultProof`. Proved here instead, by
   the same method: `consGraph` (`…SparsePairGraphProof`, public) + `graphInputTransport` +
   `valueUnique fieldCons` gives two-argument congruence of `rawCons`; `auxiliaryTerm` and
   `addressTerm` are literal nests of `rawCons`/`consTerm` (expected definitional; the gate decides).
4. Move the held least call to `![c,e,aux d e l a]` by `graphInputTransport`, build
   `outputReport least c e (aux d e l a) (addressTerm c e m)` (G02's `outputFromLeast`, re-proved
   privately), apply `coherent` (`…SparseApplicationReinstallReportCasesProof`, public) against the
   row's own output report: `y = addressTerm c e m`; then address congruence back to `ctx, cod`.

So NO missing ingredient is expected: no uniqueness-of-reports premise, no injectivity of
`addressTerm`, no type guard. Statements:

- held-least form: two operand reports + `leastGraph … m` + acceptance of `y` ⊢ `eqn y (addressTerm ctx cod m)`;
- continuation form on #1440's exact premises: the continuation additionally receives, for every
  `y` of the extended context, the internal implication `accepted(qf,qa,y) → y = addressTerm ctx cod m`
  (via `Derivation.weakening` + `implicationIntroduction`); and its `tv := TV` variant.

Open expectations for the gate: (a) `auxiliaryTerm`/`addressTerm` unify with nested `rawCons` for
`consEqual`; (b) `simp only [programRename,threeRename,sucRelabel,auxiliaryRename]` normalises the
renamed least call.

### Targets (frozen before proof authoring)

- `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityTargets.lean`
  sha256 `621a1ba4979ed1ff11af16036e1fe916e4db2f6d36f528a7fa4c519d5a52bfc6` (2026-11-23T01:40Z)
  - `ExactInstalledApplicationOutputFunctionality`
  - `ExactInstalledApplicationOutputFunctionalityContinuation`
  - `ExactInstalledSyntaxGuardedApplicationOutputFunctionalityContinuation`

### Receipts

- 2026-11-23T01:47Z — gate `mathlib …OutputFunctionalityProof`, attempt 1 of 1: `COMPILE_PASS` for
  Targets and Proof. Receipt `build-reports/1795398283787789332-3247930.json`
  (sha256 `b05ebc89aa20c4565d0d984375c1259669e24ea529c200e3593675f027061ddb`).
  Proof module sha256 `ce43d721f982028057feab6823cca73205cac77f7978fee54679c4cbe887ac1a`.
  Targets sha256 re-checked after the pass: unchanged.
  `#print axioms`: all three theorems `[propext, Classical.choice, Quot.sound]`.

### Failures

None. Both open expectations held: `auxiliaryTerm` / `addressTerm` unified with nested `rawCons`
for the cell congruence, and the renamed least call normalised by
`programRename, threeRename, sucRelabel, auxiliaryRename`.

### State and next

PASSED. `exact_InstalledApplicationOutputFunctionality`,
`exact_InstalledApplicationOutputFunctionalityContinuation` and
`exact_InstalledSyntaxGuardedApplicationOutputFunctionalityContinuation` are gated. Evidence in
`OUTPUT-FUNCTIONALITY-EVIDENCE.json`, scope in `OUTPUT-FUNCTIONALITY-SOURCE-MAP.md`.

No ingredient was missing. The held-least form needs only the two operand reports, the least call
and the acceptance of `y` — no type guard and no scalar acceptance. Uniqueness of the operand
reports was not assumed (it is `valueUnique` on `rawContext`, `rawDomain`, `rawCodomain`,
`rawLeast`), and injectivity of `addressTerm` was not needed (the row is entered through its field
reports, not its shell equations). The one thing not accepted under any name — congruence of
`rawCons` / `auxiliaryTerm` / `addressTerm` in all arguments — is proved privately in the proof
module (`consEqual`, `auxiliaryEqual`, `addressEqual`) from the public `consGraph`.

Still explicit (inherited, continuation forms only): the two original type guards; in the general
statement `unary tv (suc z) cod`. They are used only by #1438's scalar-acceptance conjunct.

Not done: uniqueness of the measured least itself is not stated separately (two least calls on the
same triple agree by `valueUnique` + `cancelSuc`; it is used implicitly through `coherent`). The
functionality conjunct is a per-term implication schema over `y : OTerm β`, not one internally
quantified formula.

Next: (1) package existence + functionality as a single closure statement for the carrier
`{q | unary Q.scalar (suc z) q}` if a consumer wants it in one `Prop`; (2) the two type guards —
grep for an accepted arrow-inversion law for `TV` / `refitGuard` (from `TV (rawCons dom cod)` to
`TV dom ⊓ TV cod`), still not grepped; (3) if useful downstream, promote `consEqual` to a public
support module instead of a third private copy of the method.
