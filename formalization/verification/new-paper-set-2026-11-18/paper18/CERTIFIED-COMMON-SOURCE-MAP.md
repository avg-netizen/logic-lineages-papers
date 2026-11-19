# Current paper18 m:thm:common: exact source and reuse plan

Numbered theorem: `18-standard-control-comparison/sections/certified-fragments.tex`
45–51, only **m:thm:common**. The printed statement is byte-identical to old08
lines 871–877 after removal of its new section-label prefix. This observation is
not a claim that its old register status transfers. Current numbered sparse
endpoints are already accepted in packet 064; current standard-control decision
is gated separately (SNYATKOV-DECISION) and will be reused, not supplied as a
caller premise.

- **31–43, grammar.** `CommonLayerSyntax.CommonSyntax` is literal: level
  zero uses the original BaseTerm (constants, raw variables, addition, exact
  fixed Phi, arbitrary nesting); successor syntax is natural constant plus
  a list of previous-level expressions with coefficients stored as a+1.
  The list may be empty and there is no open upper remainder. The typed
  common semantics recurse down the tail of a finite list of genuine
  nonzero-limit heads, preserving all raw valuation identities rather than
  treating distinct occurrences independently. The finite list may have
  completely different heads at different levels, and no \(\omega^\omega\)
  bound or polynomial-head requirement.
- **45–50, all three comparisons.** `ExactPointwise` pins the existing
  typed source truth and exact raw-variable *membership set* (not list
  order/count), the actual base formula's literal numeric calibration, and
  the total code-output program. The signed difference of the two actual
  source values has `Int.sign = -1, 0, 1` for the printed <, =, >, with the
  checked comparator even handling every integer desired sign and every Nat
  valuation. Its stronger statement includes the printed positive domain.
- **92–94, exact retained names.** The current proof appends an explicit
  clarification that canceled names are restored by conjoining `x=x`.
  `CommonHeadExactVariables.formula` already conjoins the finite literal
  set of original-name self-equalities via
  `BalancedExactVariables.variablesFormula`; its distinct variables are
  read from both unchanged source operands before comparison compilation.
  These conjuncts are retained even when cancellations make the result a
  constant. Actual source semantics and literal output code include this
  padding, and the new comparator requires exact, not one-way, free names.
- **49–50 and 97–104, arbitrary Boolean/quantifier closure.**
  `CommonHeadFirstOrder.Formula` permits negation, conjunction, Nat and
  positive existential binders at arbitrary nesting and with raw name
  shadowing. The usual Boolean operations and both universal domains use
  these constructs; `ExactTranslation` requires the explicit universal
  calibration. Every atom retains its own genuine finite head certificate.
  Translation within the Boolean tree keeps the original name and
  `Function.update`; a positive existential is literally guarded by 0<x.
  The emitted radix-five source code is the exact translated SourceFormula,
  with full typed truth and exact syntactic free-variable-set preservation.
- **Actual decidability.** `ActualClosedAnswer` independently states the
  concrete composition of that raw translator with the actual
  `SixSol20261112.SourceDecision.answer` checked by current
  `SnyatkovDecisionStatementChecks.actualClosedAnswer`. Prove the translated
  formula is closed by exact name membership, apply the current arithmetic
  answer to the *same* encoded translated formula at every valuation, then apply
  actual source translation. The program is total on raw codes, including
  the existing malformed atomic default, not a promise of malformed-raw
  semantic correctness. No premise of effectively supplied solver,
  generation or arbitrary expanded-language decision enters.
  The theorem requires only genuine coverage of certified comparisons, so
  semantic correctness is admitted on typed certified *closed* formulas,
  while the original open pointwise clause is explicit separately.

The actual old08 CommonHeadExactVariables and CommonHeadFirstOrder proofs
were dependencies of BUILD-046; the current proof will explicitly assemble
the checked source/translation clauses and derive the concrete decision from
current Snyatkov, not alias old08's aggregate theorem. Preserve the new frozen
comparator, exact source bytes, old accepted proofs and failed drafts.
Require independent scope before proof, target-only preflight first, sole
fixed-limit native gate, compiler-free recursive actual artifact/axiom evidence
and independent final source/math review before numbered adoption. Balanced
comparison is a distinct packet and is not promoted by this endpoint.
