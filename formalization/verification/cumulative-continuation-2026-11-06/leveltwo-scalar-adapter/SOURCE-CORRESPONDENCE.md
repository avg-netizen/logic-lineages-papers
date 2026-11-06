# Level-two scalar adapter

Baseline: `089f17230b13b08898033931baecaf4226effb31`.

This addition pays one translation interface in paper08 `thm:leveltwo`,
`08-multivariate-collapse-comparison/paper.tex`, lines 802–820. The existing
source-class theorem already proves that the actual canonical scalar's fixed
heads are nonzero polynomial limits. The existing polynomial graph theorem
already supplies total functional graphs. Neither result is reproved here.

## Exact scope

The adapter converts the original `Source.ForwardTranslation.Scalar` into
`PolynomialGraphCompletion.Expr`. It preserves each ordered original variable
occurrence and the normalized notation of the exact head `omega ⊗ c`.
Its value equality uses one shared valuation, including repeated names.
The source-facing target derives polynomiality from the complete internal
level bound, covering every original subterm and binder type, and retains the
actual successful canonical assignment and scalar extraction.

The total numeric radix conversion is calibrated both to normalized scalar
codes and to literal source-syntax codes, whose closed positive heads are
normalized by the existing primitive-recursive evaluator. It emits exactly
the existing primitive-recursive graph package. A result symbol may coincide
with a source name; the graph theorem preserves that correlation rather than
asserting unconditional satisfiability in that case.

## Boundaries

- The name theorem is relative to the supplied indexing function. A consumer
  representing independent source names must use the existing faithful
  ground-component indexing; injectivity is not assumed or proved here.
- Scalar and graph semantics hold on all natural valuations. The eventual
  source counterexample must impose positivity on original names, with fresh
  graph nodes quantified over all naturals.
- The source-facing semantic theorem permits every existing structural policy.
  Numeric effectivity here concerns the explicit scalar-syntax input; no
  arbitrary policy function is asserted computable.
- Pairwise positive-coordinate flags, weak/WW-strict/equality counterexample
  assembly, whole original-source numeric compilation and existential decision
  remain separate. This does not promote `thm:leveltwo`, guards, rows, or the
  existential solver. No existing target, manuscript, dependency, checker,
  root import or CI configuration is changed.

## Reused endpoints

- `WWSourceClassesFullProof.actualSourceClasses`
- `WWScalarTranslationProof.scalarTranslationSound`
- `WWScalarSyntaxCodeProof.scalarSyntaxNormalizationCorrect`
- `WWScalarSyntaxCodeProof.scalarSyntaxNormalizationPrimitiveRecursive`
- `PolynomialGraphCompletion.ExpressionSemanticStatementChecks.correlated_existential_graph`
- `PolynomialGraphCompletion.ExpressionProgramStatementChecks.literal_graph_compiler`
- `PolynomialGraphCompletion.ExpressionProgramStatementChecks.actual_numeric_program`
