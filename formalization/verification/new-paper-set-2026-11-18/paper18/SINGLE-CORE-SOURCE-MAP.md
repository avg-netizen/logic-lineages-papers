# Current18 single-core: source-complete proposed comparator

Source: `18-standard-control-comparison/sections/certified-fragments.tex`,
`m:thm:single-core`, including the preceding literal grammar. Archived08
`thm:single-core` has the same grammar, row, quantifiers, sign-formula and
universal-decision conclusions; only section/label references changed.

## Exact interface
- `MultivariatePositiveExpr`: natural constants, original indexed raw names,
  addition and arbitrary fixed nonzero limit heads on arbitrarily nested cores.
  Fixed nonnegative multiples are finite repeated addition; zero multiples
  are the constant-zero tree and hence have empty actual support. There is no
  subtraction or exposed f constructor inside the core. `multivariatePositiveValid`
  retains names < d and true limit heads below epsilonZero.
- `actualProfileHead rho n = actualCollapse (rho.repr + n)` uses the original
  fixed control `Phi n = fastControl 5 (n+100)`, not a chosen permitted control.
- `SingleCoreRow` literally contains K, r and finite atoms (head, integer q,
  positive natural multiplier a, natural offset c). Its value is exactly
  K+r*E+sum q*h(head)(a*E+c). Arbitrary repeated triples, zero/negative q,
  empty atom lists, and zero linear coefficient are admitted.
- Sign codes 0/1/2 mean negative/zero/positive. `SignFormulas` requires an
  actual finite Presburger AST whose encoded bytes equal the concrete compiler
  output, no new raw variable, and equivalence at EVERY positive valuation.
  Original repeated names are shared. Unused names remain unrestricted.
  The source says 'in the original raw variables', not exact syntactic support
  equality (unlike its common-head theorem); no fresh names is the contract.
- `Programs` proves joint total Computable of the actual encoded compiler and
  universal sign-mask program. Invalid codes have total outputs too; semantic
  assertions only need the literal source-validity conditions.
- `UniversalComparison` gives all positive valuations, no range or independence
  premise on E, covering allowed masks [0], [1], [2], [0,1], [1,2], etc.
  Empty support is included and handled by the single empty point.

## Legitimate exact supplier reuse
`OrdinalComparison.SingleCorePresburger.full` supplies the complete three
expanded clauses, not a conditional arithmetic decision class. Its imports
prove actual code computation, finite support box semantics, and core domination.
Its tail is obtained through the checked arbitrary-head one-variable comparison
algorithm on the signed row in a formal single input, then transferred to E.
This is an alternative effective proof, not the printed optimized lexicographic
triple threshold; the theorem does not prescribe that threshold. No Snyatkov
first-order decision theorem is assumed or needed. Full recursive native
evidence and independent source review remain mandatory before promotion.

## Exclusions
No common-head/balanced full quantified claim, general free-parameter QE,
source canonical assignment comparison, arbitrary additional open remainder,
variable ordinal heads, nonlinear E dependence, or graph definition of E.

## Candidate prepared after independent pre-scope approval
`StandardControlCurrent.SingleCoreStatementChecks` supplies the three exact
expanded clauses from `SingleCorePresburger.programs`, `.output`, and
`.universal_correct`, and conjoins them as `full`. No new semantics or target
change. All four actual aliases print axiom closures. Native gate is pending.
