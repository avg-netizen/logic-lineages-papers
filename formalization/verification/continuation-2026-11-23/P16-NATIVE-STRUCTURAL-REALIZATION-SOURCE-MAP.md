# Paper 16: literal typed structural realization supplier

Source-only support for `lem:realization`, ordinals.tex 434–448, and the
typed lambda/applications used by its finite-type extractors (525–558).
The already checked generic ordinal closure (#498), actual one-step closed
beta (#496), and native closed application (#493) are not reasserted as
independently new results. In particular the older mixed ordinal draft
contains an introduction theorem for one lambda, not a structural
induction through a typed source tree.

- `NativeStructuralRealizationSyntax` assigns a binder-indexed tree to
  the fragment of finite semantic types used by the paper. Erasure is
  literal original `Spine.Expr`: bound index, `NativeReduction.app`, lambda,
  or an explicitly supplied original `ClosedNativeTerm`. The tree is
  not an alternative term language or alternate reduction relation.
- `ClosingProof` checks original annotated typing, creates actual closed
  simultaneous instances of every such tree and proves their underlying
  value is the literal `Spine.substitute` with the whole typed nearest-first
  `Spine.Args` block. Variable reads follow its actual index. Application
  is the same original closed application; closed constants are unchanged.
  Ordinary syntax, validity, absence of free names, and native syntax are
  proved, not put into the theorem as assumed instance outputs.
- `BetaProof` uses exactly one original native beta step on the closed
  substituted lambda. The previously checked literal block-composition
  law identifies the actual right-hand side with simultaneous substitution
  in the original body using the extended environment. Both the reduction
  and the original confined strict edge are retained.
- `Proof` derives the structural realization rule for variables, application,
  lambda and literal closed constants. At arrows the model uses all functions;
  its arrow realization clause and strict-backward closure are stated inputs,
  and every chosen constant's realization is an explicit input. The proof
  assumes neither the typed structural lemma nor any results for these
  constructor instances. No monotonicity, continuity, arbitrary primitive
  native constant semantics, or strict relation different from `NativeBelow`.
  The last layer can be instantiated with actual ordinal realizers once a
  compatible separately gated mixed interface is available.

Run the named checks independently: first `NativeStructuralRealizationLiteralChecks`
(original typing, literal substitution laws and exact original one-step beta),
then `NativeStructuralRealizationChecks` (structural induction only). The
closure is core-only and does not import Mathlib's `Ordinal.Rank`. No numbered
promotion, Mathlib/legacy boundary migration, or redispatch of the old
mixed ordinal gate.
