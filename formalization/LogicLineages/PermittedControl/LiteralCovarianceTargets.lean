module
public import LogicLineages.PermittedControl.LiteralCovarianceDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.LiteralCovarianceTargets
open OrdinalComparison Source Source.AdmissibleSum LiteralCovariance

def OccurrenceSizeClosure : Prop :=
  ∀ (Γ Δ : List Ty) (σ : Ty) (ρ : TailSubstitution Γ Δ) (t : OrdinalExpression (σ::Γ)),
    ordinalHeadOccurs (apply (lift σ ρ) t) = ordinalHeadOccurs t ∧
    ordinalHeadFree (apply (lift σ ρ) t) = ordinalHeadFree t ∧
    ordinalPartialSize (apply (lift σ ρ) t) = ordinalPartialSize t ∧
    ordinalHeadClosure (apply (lift σ ρ) t) = apply ρ (ordinalHeadClosure t)

def PartialCovariance : Prop :=
  ∀ (Γ Δ : List Ty) (σ : Ty) (ρ : TailSubstitution Γ Δ) (p : Policy)
    (i : Nat) (t : OrdinalExpression (σ::Γ)),
    AdmissiblePartial.run p i (apply (lift σ ρ) t) =
      (AdmissiblePartial.run p i t).map (fun v j => apply ρ (v j))

def FactorCovariance : Prop :=
  ∀ (Γ Δ : List Ty) (σ : Ty) (ρ : TailSubstitution Γ Δ) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
    2^(σ.level+1) * ((List.ofFn (fun j => apply (lift σ ρ) (h j))).map ordinalPartialSize).sum =
      2^(σ.level+1) * ((List.ofFn h).map ordinalPartialSize).sum

def DeltaCovariance : Prop :=
  ∀ (Γ Δ : List Ty) (σ : Ty) (ρ : TailSubstitution Γ Δ) (p : Policy) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
    delta p (fun j => apply (lift σ ρ) (h j)) =
      (delta p h).map (fun v j => apply ρ (v j))

def AbstractionCovariance : Prop :=
  ∀ (Γ Δ : List Ty) (σ : Ty) (ρ : TailSubstitution Γ Δ) (p : Policy) (m : Nat)
    (h : OrdinalVector (σ::Γ) m),
    AdmissibleAssignment.abstraction p (fun j => apply (lift σ ρ) (h j)) =
      (AdmissibleAssignment.abstraction p h).map (fun v j => apply ρ (v j))

def FullLiteralCovariance : Prop :=
  OccurrenceSizeClosure ∧ PartialCovariance ∧ FactorCovariance ∧
  DeltaCovariance ∧ AbstractionCovariance

end LogicLineages.PermittedControl.LiteralCovarianceTargets
