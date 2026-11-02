module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsStatementChecks

theorem fixedSupNatural : NaturalLayerBoundsTargets.SupNatural := NaturalLayerBoundsProof.supNatural
theorem fixedInfNatural : NaturalLayerBoundsTargets.InfNatural := NaturalLayerBoundsProof.infNatural
theorem fixedSupUniversal : NaturalLayerBoundsTargets.SupUniversal := NaturalLayerBoundsProof.supUniversal
theorem fixedInfUniversal : NaturalLayerBoundsTargets.InfUniversal := NaturalLayerBoundsProof.infUniversal
theorem fixedSupRestriction : NaturalLayerBoundsTargets.SupRestriction := NaturalLayerBoundsProof.supRestriction
theorem fixedInfRestriction : NaturalLayerBoundsTargets.InfRestriction := NaturalLayerBoundsProof.infRestriction

#print axioms fixedSupNatural
#print axioms fixedInfNatural
#print axioms fixedSupUniversal
#print axioms fixedInfUniversal
#print axioms fixedSupRestriction
#print axioms fixedInfRestriction
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering
end LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsStatementChecks
