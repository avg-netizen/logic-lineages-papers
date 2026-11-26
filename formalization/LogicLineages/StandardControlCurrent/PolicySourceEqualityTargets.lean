module
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicySourceEqualityTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.OriginalDomain

def GroundDomain : Prop :=
  (∀ (Γ : List Ty), (∀ σ ∈ Γ, σ=Ty.ground) →
    ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0<ρ c) →
      ∃ s : AdmissibleSubstitution Γ, ∀ c, valuation s c=(ρ c : Ordinal)) ∧
  (∀ (Γ : List Ty), (∀ σ ∈ Γ, σ=Ty.ground) →
    ∀ s : AdmissibleSubstitution Γ, ∃ ρ : OrdinalComponent Γ → Nat,
      (∀ c, 0<ρ c) ∧ ∀ c, valuation s c=(ρ c : Ordinal))

def Programs : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (fun x : Nat × Nat × Nat => PolicySourceEquality.compileSyntax p x.1 x.2.1 x.2.2) ∧
  Computable (fun x : Nat × Nat × Nat => PolicySourceEquality.equalityCode p x.1 x.2.1 x.2.2)

def TypedEquality : Prop := ∀ (p : Policy) (Γ : List Ty), (∀ σ ∈ Γ, σ=Ty.ground) →
  ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
    PolicySourceEquality.equalityCode p Γ.length (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b)=true ↔
      ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
        AdmissibleAssignment.assignment p a=some av ∧ AdmissibleAssignment.assignment p b=some bv ∧
        ∀ (s : AdmissibleSubstitution Γ) (j : Nat),
          PolicySourceEquality.vectorAt av s j=PolicySourceEquality.vectorAt bv s j

/-- Full raw-source correspondence, with false for malformed input rather
than vacuous truth; repeated names share their actual context coordinates. -/
def RawEquality : Prop := ∀ (p : Policy) (d n m : Nat),
  PolicySourceEquality.equalityCode p d n m=true ↔
    ∃ (τ υ : Ty) (a : OriginalTerm (List.replicate d Ty.ground) τ)
      (b : OriginalTerm (List.replicate d Ty.ground) υ)
      (av : OrdinalVector (List.replicate d Ty.ground) τ.level)
      (bv : OrdinalVector (List.replicate d Ty.ground) υ.level),
      SyntaxCode.encodeTerm a=n ∧ SyntaxCode.encodeTerm b=m ∧
      AdmissibleAssignment.assignment p a=some av ∧ AdmissibleAssignment.assignment p b=some bv ∧
      ∀ (s : AdmissibleSubstitution (List.replicate d Ty.ground)) (j : Nat),
        PolicySourceEquality.vectorAt av s j=PolicySourceEquality.vectorAt bv s j

/-- Complete current cor:source-equality under any fixed computable policy,
with original domains and all type levels, plus exact raw input semantics. -/
def Full : Prop := GroundDomain ∧ Programs ∧ TypedEquality ∧ RawEquality
end LogicLineages.StandardControlCurrent.PolicySourceEqualityTargets
