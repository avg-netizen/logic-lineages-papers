module
public import LogicLineages.OrdinalComparison.WWTypedPartialDefinitions
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDefinitions
public import Mathlib.SetTheory.Cardinal.ToNat

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSourceDomain
open OrdinalComparison Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-! Actual Paper17 B/C/C^x classes parameterized by the collapse control.
No semantic closure or success theorem is a structure field. -/
abbrev ClosedExpression := LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term Empty

noncomputable def closedValue (ctrl : Nat → Nat) (t : ClosedExpression) : Ordinal.{0} :=
  ParametricSourceSuccessor.denoteWith ctrl (fun x => nomatch x) t

noncomputable def finiteValue (a : Ordinal.{0}) : Nat := a.card.toNat

inductive ClosedGrade (ctrl : Nat → Nat) : Nat → ClosedExpression → Prop where
  | one (i : Nat) : ClosedGrade ctrl i .one
  | omega (i : Nat) (hi : 0 < i) : ClosedGrade ctrl i .omega
  | add {i : Nat} {f g : ClosedExpression} :
      ClosedGrade ctrl i f → ClosedGrade ctrl i g → ClosedGrade ctrl i (.add f g)
  | emul {i : Nat} {f g : ClosedExpression} :
      0 < i → ClosedGrade ctrl (i + 1) f → ClosedGrade ctrl i g → ClosedGrade ctrl i (.emul f g)
  | collapse {f g : ClosedExpression} :
      ClosedGrade ctrl 1 f → ClosedGrade ctrl 0 g →
      actualOrdinalNorm (closedValue ctrl f) ≤ fastControl 2 (finiteValue (closedValue ctrl g)) →
        ClosedGrade ctrl 0 (.collapse f g)
  | promote {i : Nat} {h : ClosedExpression} :
      0 < i → ClosedGrade ctrl 0 h → ClosedGrade ctrl i h

structure AdmissibleSubstitution (ctrl : Nat → Nat) (Γ : List Ty) where
  vector : {τ : Ty} → Variable Γ τ → Fin (τ.level + 1) → ClosedExpression
  graded : ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
    ClosedGrade ctrl j.val (vector x j)
  bounded : ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
    actualOrdinalNorm (closedValue ctrl (vector x j)) ≤
      actualOrdinalNorm (closedValue ctrl (vector x 0))

noncomputable def valuation (ctrl : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ) :
    OrdinalComponent Γ → Ordinal.{0}
  | ⟨_, x, j⟩ => closedValue ctrl (ρ.vector x j)

noncomputable def expressionValue (ctrl : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ)
    (t : OrdinalExpression Γ) : Ordinal.{0} := ParametricSourceSuccessor.denoteWith ctrl (valuation ctrl ρ) t

/-- The original universally quantified collapse side condition. -/
def CollapseNormPremise (ctrl : Nat → Nat) {Γ : List Ty} (f g : OrdinalExpression Γ) : Prop :=
  ∀ ρ : AdmissibleSubstitution ctrl Γ,
    actualOrdinalNorm (expressionValue ctrl ρ f) ≤ fastControl 2 (finiteValue (expressionValue ctrl ρ g))

inductive AmbientGrade (ctrl : Nat → Nat) (Γ : List Ty) : Nat → OrdinalExpression Γ → Prop where
  | one (i : Nat) : AmbientGrade ctrl Γ i .one
  | omega (i : Nat) (hi : 0 < i) : AmbientGrade ctrl Γ i .omega
  | var {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)) :
      AmbientGrade ctrl Γ j.val (.var ⟨τ, x, j⟩)
  | add {i : Nat} {f g : OrdinalExpression Γ} :
      AmbientGrade ctrl Γ i f → AmbientGrade ctrl Γ i g → AmbientGrade ctrl Γ i (.add f g)
  | emul {i : Nat} {f g : OrdinalExpression Γ} :
      0 < i → AmbientGrade ctrl Γ (i + 1) f → AmbientGrade ctrl Γ i g →
        AmbientGrade ctrl Γ i (.emul f g)
  | collapse {f g : OrdinalExpression Γ} :
      AmbientGrade ctrl Γ 1 f → AmbientGrade ctrl Γ 0 g → CollapseNormPremise ctrl f g →
        AmbientGrade ctrl Γ 0 (.collapse f g)
  | promote {i : Nat} {h : OrdinalExpression Γ} :
      0 < i → AmbientGrade ctrl Γ 0 h → AmbientGrade ctrl Γ i h

inductive HeadGrade (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) : Nat → OrdinalExpression (σ :: Γ) → Prop where
  | one (i : Nat) : HeadGrade ctrl Γ σ i .one
  | omega (i : Nat) (hi : 0 < i) : HeadGrade ctrl Γ σ i .omega
  | var {τ : Ty} (x : Variable (σ :: Γ) τ) (j : Fin (τ.level + 1)) :
      HeadGrade ctrl Γ σ j.val (.var ⟨τ, x, j⟩)
  | add {i : Nat} {f g : OrdinalExpression (σ :: Γ)} :
      HeadGrade ctrl Γ σ i f → HeadGrade ctrl Γ σ i g → HeadGrade ctrl Γ σ i (.add f g)
  | emul {i : Nat} {f g : OrdinalExpression (σ :: Γ)} :
      0 < i → HeadGrade ctrl Γ σ (i + 1) f → HeadGrade ctrl Γ σ i g →
        HeadGrade ctrl Γ σ i (.emul f g)
  | collapse {f g : OrdinalExpression (σ :: Γ)} :
      HeadGrade ctrl Γ σ 1 f → HeadGrade ctrl Γ σ 0 g → CollapseNormPremise ctrl f g →
        HeadGrade ctrl Γ σ 0 (.collapse f g)
  | promote {i : Nat} {h : OrdinalExpression (σ :: Γ)} :
      0 < i → HeadGrade ctrl Γ σ 0 h → ordinalHeadFree h = true → HeadGrade ctrl Γ σ i h


end LogicLineages.PermittedControl.SelectedSourceDomain
