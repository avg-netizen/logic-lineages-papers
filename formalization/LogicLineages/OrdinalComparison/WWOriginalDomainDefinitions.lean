module
public import LogicLineages.OrdinalComparison.WWTypedPartialDefinitions
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions
public import Mathlib.SetTheory.Cardinal.ToNat

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-! Original public Wilken--Weiermann, LMCS 8(1:19), 2012,
arXiv:1203.0115v2, Definitions 2.5--2.9. These are the actual norm-admissible
syntactic domains, separate from the earlier generated grammar and exact
partial-recursion admission. All finite-context variables are assigned closed
bounded B-vectors. No target closure or weak inequality is a structure field.
The finite scalar interpretation through card.toNat requires the separate B0
finiteness theorem; it is not a claim about arbitrary ordinal expressions. -/

abbrev ClosedExpression := LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term Empty

noncomputable def closedValue (t : ClosedExpression) : Ordinal.{0} :=
  denote (fun x => nomatch x) t

noncomputable def finiteValue (a : Ordinal.{0}) : Nat := a.card.toNat

inductive ClosedGrade : Nat → ClosedExpression → Prop where
  | one (i : Nat) : ClosedGrade i .one
  | omega (i : Nat) (hi : 0 < i) : ClosedGrade i .omega
  | add {i : Nat} {f g : ClosedExpression} :
      ClosedGrade i f → ClosedGrade i g → ClosedGrade i (.add f g)
  | emul {i : Nat} {f g : ClosedExpression} :
      0 < i → ClosedGrade (i + 1) f → ClosedGrade i g → ClosedGrade i (.emul f g)
  | collapse {f g : ClosedExpression} :
      ClosedGrade 1 f → ClosedGrade 0 g →
      actualOrdinalNorm (closedValue f) ≤ fastControl 2 (finiteValue (closedValue g)) →
        ClosedGrade 0 (.collapse f g)
  | promote {i : Nat} {h : ClosedExpression} :
      0 < i → ClosedGrade 0 h → ClosedGrade i h

structure AdmissibleSubstitution (Γ : List Ty) where
  vector : {τ : Ty} → Variable Γ τ → Fin (τ.level + 1) → ClosedExpression
  graded : ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
    ClosedGrade j.val (vector x j)
  bounded : ∀ {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)),
    actualOrdinalNorm (closedValue (vector x j)) ≤
      actualOrdinalNorm (closedValue (vector x 0))

noncomputable def valuation {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) :
    OrdinalComponent Γ → Ordinal.{0}
  | ⟨_, x, j⟩ => closedValue (ρ.vector x j)

noncomputable def expressionValue {Γ : List Ty} (ρ : AdmissibleSubstitution Γ)
    (t : OrdinalExpression Γ) : Ordinal.{0} := denote (valuation ρ) t

/-- The original universally quantified collapse side condition. -/
def CollapseNormPremise {Γ : List Ty} (f g : OrdinalExpression Γ) : Prop :=
  ∀ ρ : AdmissibleSubstitution Γ,
    actualOrdinalNorm (expressionValue ρ f) ≤ fastControl 2 (finiteValue (expressionValue ρ g))

inductive AmbientGrade (Γ : List Ty) : Nat → OrdinalExpression Γ → Prop where
  | one (i : Nat) : AmbientGrade Γ i .one
  | omega (i : Nat) (hi : 0 < i) : AmbientGrade Γ i .omega
  | var {τ : Ty} (x : Variable Γ τ) (j : Fin (τ.level + 1)) :
      AmbientGrade Γ j.val (.var ⟨τ, x, j⟩)
  | add {i : Nat} {f g : OrdinalExpression Γ} :
      AmbientGrade Γ i f → AmbientGrade Γ i g → AmbientGrade Γ i (.add f g)
  | emul {i : Nat} {f g : OrdinalExpression Γ} :
      0 < i → AmbientGrade Γ (i + 1) f → AmbientGrade Γ i g →
        AmbientGrade Γ i (.emul f g)
  | collapse {f g : OrdinalExpression Γ} :
      AmbientGrade Γ 1 f → AmbientGrade Γ 0 g → CollapseNormPremise f g →
        AmbientGrade Γ 0 (.collapse f g)
  | promote {i : Nat} {h : OrdinalExpression Γ} :
      0 < i → AmbientGrade Γ 0 h → AmbientGrade Γ i h

inductive HeadGrade (Γ : List Ty) (σ : Ty) : Nat → OrdinalExpression (σ :: Γ) → Prop where
  | one (i : Nat) : HeadGrade Γ σ i .one
  | omega (i : Nat) (hi : 0 < i) : HeadGrade Γ σ i .omega
  | var {τ : Ty} (x : Variable (σ :: Γ) τ) (j : Fin (τ.level + 1)) :
      HeadGrade Γ σ j.val (.var ⟨τ, x, j⟩)
  | add {i : Nat} {f g : OrdinalExpression (σ :: Γ)} :
      HeadGrade Γ σ i f → HeadGrade Γ σ i g → HeadGrade Γ σ i (.add f g)
  | emul {i : Nat} {f g : OrdinalExpression (σ :: Γ)} :
      0 < i → HeadGrade Γ σ (i + 1) f → HeadGrade Γ σ i g →
        HeadGrade Γ σ i (.emul f g)
  | collapse {f g : OrdinalExpression (σ :: Γ)} :
      HeadGrade Γ σ 1 f → HeadGrade Γ σ 0 g → CollapseNormPremise f g →
        HeadGrade Γ σ 0 (.collapse f g)
  | promote {i : Nat} {h : OrdinalExpression (σ :: Γ)} :
      0 < i → HeadGrade Γ σ 0 h → ordinalHeadFree h = true → HeadGrade Γ σ i h

end LogicLineages.OrdinalComparison.Source.OriginalDomain
