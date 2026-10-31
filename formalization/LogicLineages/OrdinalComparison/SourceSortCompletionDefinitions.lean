module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
public import LogicLineages.OrdinalComparison.SourceSuccessorCodingDefinitions
public import Mathlib.Data.Multiset.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceSortCompletion
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Actual source observation, with every coordinate interpreted under the same
natural-to-positive-raw valuation. The assignment is the full zero-history
compiler at the printed default policy, not the applicative approximation. -/
def Observation {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat)
    (t : OriginalTerm Γ .ground) (y : Nat) : Prop :=
  ∃ v : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v ∧
    denote (fun c => ((ρ c + 1 : Nat) : Ordinal)) (v 0) = ((y + 1 : Nat) : Ordinal)

def input {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat) (x : Variable Γ .ground) : Nat :=
  ρ ⟨.ground, x, 0⟩

/-- A primitive-positive formula: four actual S graph leaves, addition and
conjunction, with four existential natural witnesses. Repeated variables
remain identical typed variables; all leaves use exactly the same ρ. -/
def SortFormula {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat)
    (a b low high : Variable Γ .ground) (difference : Nat) : Prop :=
  ∃ qa qb qlow qhigh : Nat,
    Observation ρ (successorProbe a) qa ∧
    Observation ρ (successorProbe b) qb ∧
    Observation ρ (successorProbe low) qlow ∧
    Observation ρ (successorProbe high) qhigh ∧
    qa + qb = qlow + qhigh ∧ input ρ low + difference = input ρ high
end LogicLineages.OrdinalComparison.Source.SourceSortCompletion
