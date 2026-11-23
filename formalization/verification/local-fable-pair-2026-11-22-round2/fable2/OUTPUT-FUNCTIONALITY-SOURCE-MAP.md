# Paper 16: the installed application program has one output on accepted operand addresses

Continues `FRONTEND-ACCEPTANCE-SOURCE-MAP.md` (G02, record #1440) at the same `install …` route.
That step proved the installed application program accepts `(qf, qa, addressTerm ctx cod m)`; this
step proves it accepts nothing else on `(qf, qa)`. Supporting result; no numbered statement is
closed and no register item is promoted.

Gate: receipt `build-reports/1795398283787789332-3247930.json`, first attempt. Hashes and axiom
lines in `OUTPUT-FUNCTIONALITY-EVIDENCE.json`.

## Claimed

`ExactInstalledApplicationOutputFunctionality` (theorem
`exact_InstalledApplicationOutputFunctionality`) — held-least form. For the installed route
`Q := install s V TV M M0 B T base cv tv root other`, any ID1 body, context `Γ` and terms: from
derivations in `Γ` of

- `addressReport qf ctx (rawCons dom cod) fn`,
- `addressReport qa ctx dom arg`,
- `leastGraph Q.source.cover Q.exchange Q.window s ctx cod (auxiliaryTerm dom cod fn arg) m`, and
- `programGraph Q.application (suc z) ![qf, qa, y]`,

there is a derivation in `Γ` of `eqn y (addressTerm ctx cod m)`. No type guard and no scalar
acceptance is a premise of this form.

`ExactInstalledApplicationOutputFunctionalityContinuation` (theorem of the same name with
`exact_`) — continuation form on exactly #1440's premises (two type guards, `unary tv (suc z) cod`,
the two operand reports, installed-scalar acceptance of both operands). The object continuation
over `(β) (j) (Δ) (m)` receives #1440's four conjuncts unchanged and a fifth: for every
`y : OTerm β`, a derivation in `Δ` of the internal implication

`programGraph Q.application (suc z) ![qf, qa, y]  →  eqn y (addressTerm ctx cod m)`

(operands and coordinates relabelled along `j`), for the same fresh `m`.

`ExactInstalledSyntaxGuardedApplicationOutputFunctionalityContinuation`: the same at `tv := TV`,
where the result type guard is the right half of the retained syntax guard and disappears.

### How the uniqueness is obtained — every step from an accepted supplier

| Step | Supplier |
|---|---|
| acceptance of `y` ⇒ `applicationReport Q.scalar Q.least qf qa y` | forward half of `exact_InstalledApplicationReport` |
| open the six-witness block to fresh `c r d e l a` | `rowCases` (`…SparseApplicationFrontendOpenBindingProof`) |
| `ctx = c`, `fn = l`, `arg = a`, `dom = d`, `cod = e` | `valueUnique` on `rawContext`, `rawLeast` (at `qf` and at `qa`), `rawDomain`, `rawCodomain`; the caller-side domain/codomain fields from `canonicalCell` + `makeUnary` |
| held least call moved to `![c, e, auxiliaryTerm d e l a]` | `graphInputTransport` |
| `y = addressTerm c e m` | `coherent` (`…SparseApplicationReinstallReportCasesProof`) between the row's own `outputReport` and the one built from the moved least call (`reportUnfold` / `reportInstance`) |
| `addressTerm c e m = addressTerm ctx cod m` | cell congruence (below) |

Proved privately in the proof module because no accepted statement exists under any name (grep
for `eqn (rawCons …) (rawCons …)` / `eqn (auxiliaryTerm …) (auxiliaryTerm …)` finds only the
private one-argument `addressEqual` in `…SparseApplicationReinstallResultProof`):

- `consEqual`: `x = u`, `y = v` ⊢ `rawCons x y = rawCons u v`, from the public `consGraph`,
  `graphInputTransport` and `valueUnique fieldCons`;
- `auxiliaryEqual`, `addressEqual`: all-argument congruence of `auxiliaryTerm` and `addressTerm`,
  which are literal nests of that cell constructor.

## Assumed (explicit premises that remain)

- Held-least form: only the four derivations listed above. The least `m` is a premise there, not
  produced.
- Continuation forms: #1440's premises unchanged — the two original type guards
  (`TV` and `refitGuard s T` at `dom`, `cod`), and in the general statement `unary tv (suc z) cod`.
  These are consumed only by #1438's scalar-acceptance conjunct; the functionality conjunct does
  not use them.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only. No `sorry`, `axiom`, `native_decide`.

Not assumed, although the task allowed for it: uniqueness of the operand reports for a given
address (it is functionality of the field programs), injectivity of `addressTerm` (the row is
entered through its field reports, not its shell equations), any arrow guard, arrow report, shell
equation or block witness.

## Not claimed

- A single internally quantified formula `∀ y (accepted → y = …)`: the fifth conjunct is a schema
  over terms `y` of the extended context, each instance an internal implication.
- A separate statement that the measured least is unique (two least calls on one triple agree by
  `valueUnique` + `cancelSuc`; used only implicitly through `coherent`).
- Functionality in the operands (that equal or equivalent operand addresses give equal outputs),
  or anything about operands whose reports sit at different contexts.
- Removal of the two type guards; whether an accepted arrow-inversion law for `TV` /
  `refitGuard` exists was not grepped.
- Closure of the carrier `{q | unary Q.scalar (suc z) q}` under application packaged as one
  statement; existence (#1438, #1440) and functionality (this step) are separate `Prop`s sharing
  one continuation.
- Any numbered statement of Paper 16.
