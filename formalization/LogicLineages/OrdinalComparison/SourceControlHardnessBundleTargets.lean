module
public import LogicLineages.OrdinalComparison.SourceControlHardnessBundleDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceControlHardnessBundle.Targets
open Turing LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabet

def ExplicitEnumerationClock : Prop :=
  Primrec SourceBlankMachineSimulation.program ∧
  (∀ p : Table,SourceBlankMachineSimulation.program (Encodable.encode p)=p) ∧
  Primrec SourceBlankMachineSimulation.boundedH ∧
  (∀ e t : Nat, SourceBlankMachineSimulation.boundedH (e,t)=true ↔
    ∃ d n, n ≤ t ∧ Run (SourceBlankMachineSimulation.program e)
      (initial (SourceBlankMachineSimulation.program e) []) d n ∧
      step (SourceBlankMachineSimulation.program e) d=none) ∧
  (∀ e : Nat,SourceBlankMachineSimulation.Halts e ↔
    ∃ t,SourceBlankMachineSimulation.boundedH (e,t)=true) ∧
  (∀ b : Nat,SourceMachineControlNonperiodicity.gamma b=
    PerturbedControl.control b SourceBlankMachineSimulation.boundedH)

def FixedControlHardness : Prop := ∀ b : Nat,
  Primrec (SourceMachineControlNonperiodicity.gamma b) ∧
  CoREComplete (SourceGammaRestrictedReduction.Member (SourceMachineControlNonperiodicity.gamma b)) ∧
  CoREComplete (SourceGammaWeakCodedReduction.Member (SourceMachineControlNonperiodicity.gamma b)) ∧
  ¬SourceMachineControlNonperiodicity.EventuallyPeriodicParity b

def CanonicalObservation : Prop := ∀ (b : Nat) (c : Ordinal.{0} → Nat),
  ParametricActualCollapse.Equation (SourceMachineControlNonperiodicity.gamma b) c →
  ∀ (Γ : List Ty) (t : OriginalTerm Γ .ground) (ν : OrdinalComponent Γ → Nat),
  SourceMachineRawValuations.AllGround Γ → SourceGroundBinderFragment.Fragment t →
  (∃ n : Nat,ParametricCanonicalObservation.ScalarUsing c (fun k => (ν k : Ordinal)) t n) ∧
  (∀ n : Nat,ParametricCanonicalObservation.ScalarUsing c (fun k => (ν k : Ordinal)) t n ↔
    ParametricSourceEraser.Scalar (SourceMachineControlNonperiodicity.gamma b)
      (fun k => (ν k : Ordinal)) t n)
end LogicLineages.OrdinalComparison.Source.SourceControlHardnessBundle.Targets
