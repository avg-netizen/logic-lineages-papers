# Current paper18 m:thm:balanced: exact source and reuse plan

Numbered theorem: `18-standard-control-comparison/sections/certified-fragments.tex`
181–186, only **m:thm:balanced**. The printed statement is byte-identical to
old08 lines 987–992 after removal of its new section-label prefix. Scope is
established anew from the present source plus the actual compiler and logical
closures, not the historical register. Current sparse endpoints/head window
are checked 064/065, and the decision composition uses the same concrete
current fixed-control answer from SNYATKOV-DECISION as the common theorem,
not a hypothesis of decision for arbitrary additional primitives.

- **158–173, one common preceding certificate C and whole pair basis.**
  The manuscript now makes explicit that every ordered basis entry is
  certified by the SAME preceding C, rather than merely lying at one depth.
  Immutable `BalancedSyntax.Certificate (k :: Γ)` is literally
  `Certificate Γ × (Fin k → Syntax Γ)`. Both operands, each upper atom's
  argument and the whole outside remainder access the same ordered basis C.2,
  with terms interpreted at the same original valuation via C.1. There is no
  distinctness or linear independence condition on basis entries. Each stored
  head factor is a_j−1, hence each actual factor is ≥1 for every basis
  position. Outside coefficients are arbitrary naturals including 0;
  the list holds positive outer head coefficients (stored q−1), so 0
  multiples do not introduce names. `rawVariables` drops exactly the 0
  outside multiples and retains the full basis support for each positive head
  atom. An outside-only name cannot be ignored if a small-head branch relies
  on the entire positive basis. Genuine means actual nonzero-limit heads;
  no bound on ordinal size is imposed. Empty basis and empty head sum are
  both retained.
- **174–179 and 193/210–211/240–242, same-certificate affine operations.**
  New explicit explanatory prose is already paid by
  `BalancedSyntax.Affine.Targets.LiteralAffineClosure` and
  `ExactAffineSupport`: literal same-certificate constants, sums and
  nonnegative scalings with exact support including zero scale, and genuine
  expression closure. `ActualLowerAndInputs` and `ActualCanceledDescent`
  identify literal lower remainder and common-basis inputs and show that
  the all-canceled original signed row descends to actual preceding terms.
  `LowerCertificateClosure` separately freezes these supporting clauses.
- **181–185, 203–238, all three pointwise signs.** `ExactPointwise`
  retains the computed typed ordinary base formula, every genuine original
  certificate and both genuine expressions, the one original valuation
  with positivity only on its actual free support, sign of literal value
  difference (desired −1/0/1 gives the three printed relations; arbitrary
  integer desired signs are also handled), and exact free-variable-set
  equality. The checked existing compiled output uses original large guards
  and entire small support box, exact code calibration and actual total code
  computation. No new classical predicate is used as a solver.
- **247–249, exact raw names and compatible quantifiers.** The proof now
  explicitly specifies the `x=x` padding and in-place positive binder
  translation. Old accepted `BalancedExactVariables.sourceFormula` already
  appends every literal self-equality over distinct original pair names
  before cancellation, including when output is constant or impossible,
  so formula membership is exact; an empty support retains an empty
  tautology. The translated `BalancedFirstOrder.Formula` always keeps the
  complete original pair certificate per atom, ordinary Boolean structure,
  original names and their shadowing, with all positive binders realized by
  `Function.update` and 0<x guard in the same natural source structure.
  The exact positive universal dual and exact original free names are paid,
  with no assumption on an unrelated coordinate or an old shadowed value.
- **185, actual Boolean/quantified decidability.** `ActualClosedAnswer`
  independently states the exact concrete total translator/decision
  composition; same typed translation encoding, arbitrary alternation and
  truth at every starting valuation in the closed case. Apply exact syntactic
  names to prove the translation closed. The old semantic free-name
  positivity assumption is vacuous on the closed original formula, not an
  added hypothesis on its starting valuation. Positive quantifiers
  themselves provide 0<x to each bound occurrence. Computation is total on
  raw codes even when an atomic payload takes an existing malformed default;
  semantic admission is precisely genuine typed certification and closure.

The old08 BUILD-046 claims supply immutable prior implementations, not
adoption. Reassemble the pointwise, same-certificate and FO clauses from exact
proved suppliers; directly derive the decision from the current arithmetic
answer and the literal balanced translator. Require independent source/scope
review before proof, target-only preflight, fixed serialized exact native gate,
recursive source/artifact/axiom evidence and independent final. This packet
does not promote common-head, arbitrary uncertified comparisons, or any
expanded arithmetic theory.
