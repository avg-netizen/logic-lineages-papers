module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnaryChainDefinitions
public import LogicLineages.OrdinalComparison.SelectedHeadCarrierDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriers

open LogicLineages.OrdinalComparison.Source
open SourceFreeOccurrences
open CurrentUnaryChain (commonUnits)

/-- Insert one old name immediately after the fresh head, without changing
the new head's identity. -/
def insertSecond {Γ : List Ty} {σ τ : Ty} : Renaming (σ :: Γ) (σ :: τ :: Γ)
  | _, .here => .here
  | _, .there x => .there (.there x)

/-- Replace a selected free name at any original typed position by the new
same-type head. All other source names are weakened literally at the front. -/
def renameTrackedAt : {Γ : List Ty} → {σ : Ty} →
    Variable Γ σ → Renaming Γ (σ :: Γ)
  | _, _, .here => UnaryCarrier.renameTracked
  | _, _, .there F => fun x => match x with
      | .here => .there .here
      | .there y => insertSecond (renameTrackedAt F y)

/-- The literal fresh-name substitution precedes ground application, which
precedes zero closing. Type-aware syntax controls every internal binder. -/
def carrierAt {Γ : List Ty} {σ : Ty} (F : Variable Γ σ) (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1))) :
    OriginalTerm (σ :: Γ) (Ty.curriedGround 1) :=
  UnaryCarrier.closeGround (UnaryCarrier.saturate r (t.rename (renameTrackedAt F)))

/-- What a genuine current carrier realizes. No arbitrary scalar or
hypothetical source assignment is a field. -/
def Realization (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} {σ : Ty} (F : Variable Γ σ) (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level)
    (w v : OrdinalVector (σ :: Γ) 1) : Prop :=
  AdmissibleAssignment.assignment p t = some u ∧
  AdmissibleAssignment.assignment p (UnaryCarrier.saturate r (t.rename (renameTrackedAt F))) = some w ∧
  AdmissibleAssignment.assignment p (carrierAt F r t) = some v ∧
  v = GroundClosing.vector (UnaryCarrier.groundMap _) w ∧
  v 0 = GroundClosing.expression (UnaryCarrier.groundMap _) (w 0) ∧
  (∀ x : Variable (σ :: Γ) .ground,
    (⟨Ty.ground,x⟩ : PackedVariable (σ :: Γ)) ∉ freeOccurrences (carrierAt F r t)) ∧
  (⟨σ,.there F⟩ : PackedVariable (σ :: Γ)) ∉ freeOccurrences (carrierAt F r t) ∧
  ∀ (ρ : Variable Γ .ground → Nat) (μ : Variable (σ :: Γ) .ground → Nat),
    ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v 1) =
      ParametricSourceSuccessor.denoteWith f (commonUnits ρ) (u (UnaryCarrier.headIndex r))

def HasSelectedCarrier (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    {k : Nat} (F : Variable Γ (Ty.curriedGround (k+1))) (h : OrdinalExpression Γ) : Prop :=
  ∃ (r : Nat) (t : OriginalTerm Γ (Ty.curriedGround (r+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level)
    (w v : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 1),
    Realization p f F r t u w v ∧ u (UnaryCarrier.headIndex r) = h

end LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriers
