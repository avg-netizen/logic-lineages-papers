module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel
open GorbowSyntax
/-- Original five-input core call. The requested formula is arbitrary, not
restricted a priori to the double of an externally provided raw formula. -/
def acceptance {ctx : Nat} (qtag : Nat) (index fuel context formula certificate : Term ctx) : Formula ctx :=
 .equal (LiteralCheckerAcceptance.coreCall qtag index fuel context formula certificate) (.succ .zero)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel
