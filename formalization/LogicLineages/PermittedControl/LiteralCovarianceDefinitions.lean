module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.LiteralCovariance
open OrdinalComparison Source Source.AdmissibleSum
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

abbrev TailSubstitution (Γ Δ : List Ty) := OrdinalComponent Γ → OrdinalExpression Δ

def apply {Γ Δ : List Ty} (ρ : TailSubstitution Γ Δ) :
    OrdinalExpression Γ → OrdinalExpression Δ := substitute ρ

def weaken {Γ : List Ty} (σ : Ty) : OrdinalExpression Γ → OrdinalExpression (σ::Γ) :=
  ordinalExpressionRename (fun v => .there v)

def lift {Γ Δ : List Ty} (σ : Ty) (ρ : TailSubstitution Γ Δ) :
    TailSubstitution (σ::Γ) (σ::Δ)
  | ⟨_, .here, k⟩ => .var ⟨σ,.here,k⟩
  | ⟨τ, .there v, k⟩ => weaken σ (ρ ⟨τ,v,k⟩)

/-- Literal source delta alone, without the separate retained-head addend. -/
def delta {Γ : List Ty} {σ : Ty} {m : Nat} (p : Policy)
    (h : OrdinalVector (σ::Γ) m) :
    Option (OrdinalVector Γ (max (σ.level+1) m)) := do
  let ps ← AdmissibleAssignment.collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i))
  let factor := 2^(σ.level+1) * ((List.ofFn h).map ordinalPartialSize).sum
  pure fun j =>
    if j.val=0 then AdmissibleAssignment.repeated p .scalarRepeat factor (ps 0 0)
    else if hj : j.val<σ.level+2 then
      expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val,hj⟩)
    else ordinalHeadClosure (h ⟨j.val,by have := j.isLt; omega⟩)

end LogicLineages.PermittedControl.LiteralCovariance
