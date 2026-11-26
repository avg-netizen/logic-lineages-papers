# Paper 16: the installed application program accepts the measured output address

Continues `OUTPUT-ADDRESS-SOURCE-MAP.md` (G01, record #1438) at the same `install …` route. That
step listed acceptance by the application program itself under "Not claimed"; this step proves it.
Supporting result; no numbered statement is closed and no register item is promoted.

## Claimed

`ExactInstalledApplicationFrontendAcceptance` (theorem
`exact_InstalledApplicationFrontendAcceptance`). For the installed route
`Q := install s V TV M M0 B T base cv tv root other`, any ID1 body, context and terms: given the
two original type guards, the result type guard `unary tv (suc z) cod`, the two operand address
reports at one context `ctx` (`qf` reporting result `rawCons dom cod` and class `fn`, `qa` reporting
result `dom` and class `arg`) and installed-scalar acceptance of both operand addresses, every goal
follows that follows — under the object continuation over `(β) (j) (Δ) (m)` — from all four of

- `leastGraph Q.source.cover Q.exchange Q.window s ctx cod (auxiliaryTerm dom cod fn arg) m`,
- `addressReport (addressTerm ctx cod m) ctx cod m`,
- `unary Q.scalar (suc z) (addressTerm ctx cod m)`, and
- `programGraph Q.application (suc z) ![qf, qa, addressTerm ctx cod m]` — the unit graph of the
  actual installed application program on the triple, for that same fresh `m`.

The first three are G01's continuation unchanged; the fourth is new. The premises are exactly
G01's: nothing was added.

`ExactInstalledSyntaxGuardedApplicationFrontendAcceptance`: the same at `tv := TV`, where the
result type guard is the right half of the retained syntax guard and disappears.

### The four ingredients named in the G01 handoff — all derived, none assumed

| Ingredient | Status | Accepted supplier |
|---|---|---|
| `unary arrowGood (suc z) qf` | derived | `arrowGood = applyUnary cellGood rawResult`; `canonicalCell dom cod` (`…SparsePathEnvelopeOpenCellProof`) for `cellGood (rawCons dom cod)`, composed by `makeUnary` with the function report's `rawResult` conjunct |
| `arrowReports qf dom cod` | derived | same: `canonicalCell` head `dom` / tail `cod`, `makeUnary` for `rawDomain`, `rawCodomain` |
| `qf = addressTerm ctx (rawCons dom cod) fn`, with `result = rawCons dom cod` | derived | `assembleInputs` (`…SparseApplicationFrontendOpenShapeProof`), which calls `exact_OpenAddressArrowCoordinates` |
| `qa = addressTerm ctx dom arg` | derived | `assembleInputs` (its `readNode` argument equation) |

Also derived: `addressGood` and `addressReports` for both operands (literal conjuncts of
`addressReport`); the `outputReport` conjunct (G01's least call as the single existential witness,
address equation by reflexivity, via `reportUnfold` / `reportInstance`); the six-witness `block`
(accepted `supply` in `…SparseApplicationFrontendOpenBindingProof`, witnesses
`ctx, rawCons dom cod, dom, cod, fn, arg`); the final step is the backward half of
`exact_InstalledApplicationReport`.

The reason the arrow facts cost nothing: the function report already states the result slot holds
the literal `rawCons dom cod`, and `rawCons h t = suc (pairTerm h t)` is a good sparse cell with
head `h` and tail `t` for arbitrary open terms.

Two private lemmas were written in the proof module, both glue rather than new suppliers:
`parsedFromReports` (the nine parsed-input conjuncts from the two reports) and `outputFromLeast`
(output report at the literal address from a least call). No private `block` lemma was needed.

## Assumed (explicit premises)

All inherited from G01, none new:

- `unary TV (suc z) dom ⊓ unary TV (suc z) cod` and the `refitGuard s T` pair — the two original
  type guards.
- General statement only: `unary tv (suc z) cod`. Still necessary for the scalar-acceptance
  conjunct (see G01 map). It is NOT needed for the application-graph conjunct by itself — that
  conjunct uses only the two reports, the two operand acceptances and a least call — but the least
  call comes from G01's continuation, whose statement carries the guard.
- Both operand reports at one `ctx` and both operand scalar acceptances.

## Not claimed

- Discharge of the two type guards, callback/base calibration, `InstalledTupleAt` source semantics.
- A closed existential `∃y. application(qf,qa,y)`; the witness stays under the continuation.
- Uniqueness of the accepted output. Not attempted; the candidate route (forward half of the
  report, then `coherent`) is unchecked — `coherent` wants the same `ctx`, `cod` and raw term on
  both sides, so the forward half's fresh block witnesses would first have to be identified with
  the given ones.
- That every `y` accepted by the application program is scalar-accepted; only the one emitted
  address is shown to be.
- That `tv` and `TV` coincide in the source; the second statement is the instance.

## Evidence

Targets sha256 `05b5b51e5d35074f926ea1517f316495a714aff5a0783388b028529993fd3a64`, frozen and
ledgered before the proof module existed; unchanged after the pass. Proof sha256
`904d8faf4fcf9213711fd38a73583b6cc8a6d18b8a46018ffd73b179f601dfee`. Receipt
`build-reports/1795397653724718198-3233856.json`, gate attempt 1 of 1. Axioms: `propext`,
`Classical.choice`, `Quot.sound` for both theorems. See `FRONTEND-ACCEPTANCE-EVIDENCE.json`.
