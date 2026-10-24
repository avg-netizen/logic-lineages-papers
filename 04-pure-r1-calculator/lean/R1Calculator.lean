import R1Calculator.Ordinal
import R1Calculator.Patterns
import R1Calculator.Correctness
import R1Calculator.Norm
import R1Calculator.Examples

/- Standalone public entry point. Named coverage is recorded in FORMALIZATION.md.
The pure-R1 semantic characterization is proved from recursive Sigma-one
semantics and finite induced-copy constructions, without a semantic axiom. -/

#print axioms R1Calculator.endpoint_nf
#print axioms R1Calculator.principalSum_repr
#print axioms R1Calculator.endpoint_recursion
#print axioms R1Calculator.intervalCheck_correct
#print axioms R1Calculator.PatternData.check_eq_true_iff_valid
#print axioms R1Calculator.Covering.comp
#print axioms R1Calculator.InducedEmbedding.comp
#print axioms R1Calculator.coversCheck_eq_true
#print axioms R1Calculator.embedsCheck_eq_true
#print axioms R1Calculator.markedCoversCheck_eq_true
#print axioms R1Calculator.PureR1.R1_iff_global
#print axioms R1Calculator.PureR1.R1_unique_below
#print axioms R1Calculator.PureR1.sigma1Elementary_iff_finiteReflection
#print axioms R1Calculator.PureR1.endpoint_semantic
#print axioms R1Calculator.PureR1.intervalCheck_iff_sigma1
#print axioms R1Calculator.PureR1.endpoint_isGreatest
#print axioms R1Calculator.endpoint_treeWeight_bound
#print axioms R1Calculator.endpoint_treeWeight_bound_sharp
