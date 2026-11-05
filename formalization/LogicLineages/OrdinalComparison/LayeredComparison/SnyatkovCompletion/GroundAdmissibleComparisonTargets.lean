module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparisonTargets
open GroundAdmissibleComparison Source Source.OriginalDomain RecursorFreeVector

/-- Actual WW ground substitutions have exactly the positive-natural
component valuations. Gradedness and boundedness are those of the original
AdmissibleSubstitution, not added fields asserting the desired equivalence. -/
def ExactGroundValuations : Prop := ∀ (Γ : List Ty),
  (∀ σ ∈ Γ, σ = Ty.ground) →
  (∀ ρ : AdmissibleSubstitution Γ, ∃ ν : OrdinalComponent Γ → Nat,
    (∀ c, 0 < ν c) ∧ valuation ρ = fun c => (ν c : Ordinal)) ∧
  (∀ ν : OrdinalComponent Γ → Nat, (∀ c, 0 < ν c) →
    ∃ ρ : AdmissibleSubstitution Γ, valuation ρ = fun c => (ν c : Ordinal))

/-- Pointwise agreement covers every zero-padded original coordinate,
including arbitrary positive coordinates and all three comparison modes. -/
def VectorRelationAt : Prop := ∀ (Γ : List Ty) (n m mode : Nat)
  (a : OrdinalVector Γ n) (b : OrdinalVector Γ m)
  (ρ : AdmissibleSubstitution Γ) (ν : OrdinalComponent Γ → Nat),
  valuation ρ = (fun c => (ν c : Ordinal)) →
    (relation mode a b ρ ↔ sourceRelation mode a b ν)

def UniversalComparison : Prop := ∀ (Γ : List Ty),
  (∀ σ ∈ Γ, σ = Ty.ground) → ∀ (n m mode : Nat)
    (a : OrdinalVector Γ n) (b : OrdinalVector Γ m),
  (∀ ρ : AdmissibleSubstitution Γ, relation mode a b ρ) ↔
    (∀ ν : OrdinalComponent Γ → Nat, (∀ c, 0 < ν c) → sourceRelation mode a b ν)

/-- Canonical assignment existence is supplied for both unchanged original
same-type terms, without a recursor, internal-type, finiteness, or successful
compilation hypothesis. The only source restriction is the ground free context. -/
def ActualCanonicalComparison : Prop := ∀ (Γ : List Ty),
  (∀ σ ∈ Γ, σ = Ty.ground) → ∀ (τ : Ty) (a b : OriginalTerm Γ τ),
  ∃ (av bv : OrdinalVector Γ τ.level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
    ∀ mode : Nat,
      ((∀ ρ : AdmissibleSubstitution Γ, relation mode av bv ρ) ↔
        (∀ ν : OrdinalComponent Γ → Nat, (∀ c, 0 < ν c) → sourceRelation mode av bv ν))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparisonTargets
