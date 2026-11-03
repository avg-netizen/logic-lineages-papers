module
public import LogicLineages.OrdinalComparison.SourceSignedPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SignedPair.StatementChecks

theorem fixed_signed_pair_compiler : Targets.SignedPairCompiler := Proof.signedPairCompiler
theorem fixed_monomial_adapter : Targets.MonomialAdapter := Proof.monomialAdapter

#print axioms fixed_signed_pair_compiler
#print axioms fixed_monomial_adapter
end LogicLineages.OrdinalComparison.Source.SignedPair.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SignedPair
