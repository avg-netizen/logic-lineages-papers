module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Definitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore
open GorbowSyntax
/-- Both directions at the SAME current bound and same original input tuple.
The outer call is the real bounded-search verifier, the inner call the actual
original core with its explicitly saturated axiom leaf. -/
def equivalence {ctx : Nat} (vtag qtag : Nat) (index fuel context formula certificate : Term ctx) : Formula ctx :=
 let outer := SixSol20261112.Fuel.success vtag index fuel context formula certificate
 let inner := SaturatedCoreFuel.acceptance qtag index fuel context formula certificate
 .conj (.imp outer inner) (.imp inner outer)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore
