module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainDefinitions
public import LogicLineages.OrdinalComparison.SelectedAffineHeadDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAffineHeads

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdditiveHeadTree HeadFiniteSurplus
open CurrentUnaryChain (commonUnits)

/-- Actual recursive syntactic absence of a collapse, including both ExpProd
children; it is not an arbitrary expression's grade or value. -/
def collapseFree {Γ : List Ty} : OrdinalExpression Γ → Bool
  | .var _ | .zero | .one | .omega => true
  | .add a b | .emul a b => collapseFree a && collapseFree b
  | .collapse _ _ => false

/-- Complete selected positive head/partial conclusion interpreted at the
same current control and literal common-unit valuation. -/
def HeadConclusion {k : Nat} {Γ : List Ty} (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) : Prop :=
  HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h ∧
  GeneratedOrdinalGrade (Ty.curriedGround (k+1) :: Γ) 1 h ∧
  ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
    AdmissiblePartial.run p 1 h = some v ∧
    GeneratedOrdinalGrade Γ 1 (v (outputOne k)) ∧
    GeneratedOrdinalGrade Γ 2 (v (outputTwo k)) ∧
    0 < secondCount h ∧
    (surplus h = 0 ↔ h = .var ⟨_,.here,UnaryCarrier.headIndex k⟩) ∧
    ∀ (ρ : Variable (Ty.curriedGround (k+1) :: Γ) .ground → Nat)
      (μ : Variable Γ .ground → Nat),
      ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v (outputOne k)) =
        ParametricSourceSuccessor.denoteWith f (commonUnits ρ) h + (surplus h : Ordinal) ∧
      ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v (outputTwo k)) = (secondCount h : Ordinal) ∧
      (Ordinal.omega0 ≤ ParametricSourceSuccessor.denoteWith f (commonUnits ρ) h → 1 ≤ surplus h)

end LogicLineages.ControlSensitivityCurrent.CurrentAffineHeads
