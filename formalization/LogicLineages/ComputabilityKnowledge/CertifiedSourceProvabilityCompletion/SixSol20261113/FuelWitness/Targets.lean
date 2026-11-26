module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel
/-- Exact internal extraction for the ACTUAL literal saturated verifier.
The core is arbitrary: no Boolean range, native calibration, or core-fuel
monotonicity is assumed. Its actual installed copy is specified explicitly. -/
def InternalExtraction : Prop := ∀ n (p : Program n) (vtag qtag : Nat) (q0 : Program 5),
 (nodes p)[vtag]? = some ⟨5,verifier q0⟩ →
 (nodes p)[qtag]? = some ⟨5,q0⟩ →
 ∀ ctx (index fuel context formula certificate : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (success vtag index fuel context formula certificate)
   (boundedCore qtag index fuel context formula certificate)))
/-- The reverse internal direction at the SAME outer bound, all original
runtime inputs retained. No external finite-fuel enumeration/reflection. -/
def InternalInjection : Prop := ∀ n (p : Program n) (vtag qtag : Nat) (q0 : Program 5),
 (nodes p)[vtag]? = some ⟨5,verifier q0⟩ →
 (nodes p)[qtag]? = some ⟨5,q0⟩ →
 ∀ ctx (index fuel context formula certificate : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (boundedCore qtag index fuel context formula certificate)
   (success vtag index fuel context formula certificate)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.Targets
