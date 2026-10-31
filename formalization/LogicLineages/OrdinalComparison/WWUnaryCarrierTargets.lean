module
public import LogicLineages.OrdinalComparison.WWUnaryCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnaryCarrier.Targets
open AdmissibleAssignment OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def FreshRename : Prop := ∀ (Γ : List Ty) (σ : Ty),
  @renameTracked Γ σ σ .here = .here ∧
  (∀ (τ : Ty) (x : Variable Γ τ), @renameTracked Γ σ τ (.there x) = .there (.there x)) ∧
  (∀ x : Variable (σ :: Γ) σ, renameTracked x ≠ .there .here)

def Saturation : Prop := ∀ (Γ : List Ty) (r : Nat)
    (t : OriginalTerm Γ (Ty.curriedGround (r+1))),
  ∃ u : OrdinalVector Γ (Ty.curriedGround (r+1)).level,
  ∃ v : OrdinalVector Γ 1,
    assignment OrdinalSyntax.defaultPolicy t = some u ∧
    assignment OrdinalSyntax.defaultPolicy (saturate r t) = some v ∧
    ∀ ν : OrdinalComponent Γ → Ordinal, denote ν (v 1) = denote ν (u (headIndex r))

/-- All positive fields of arbitrary supplied original sources are independent
of ground captures when functional names receive their common unit vectors.
The entire closed assignment, including its scalar, is the actual substituted
vector. There is no reset of any coordinate to a synthetic source value. -/
def CaptureClosing : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  ∃ u v : OrdinalVector Γ τ.level,
    assignment OrdinalSyntax.defaultPolicy t = some u ∧
    assignment OrdinalSyntax.defaultPolicy (closeGround t) = some v ∧
    v = GroundClosing.vector (groundMap Γ) u ∧
    ∀ (ρ μ : Variable Γ .ground → Nat) (j : Fin (τ.level+1)), 0 < j.val →
      expressionValue (UnitObservation.substitution μ) (v j) =
        expressionValue (UnitObservation.substitution ρ) (u j)

/-- Supplied actual-operator carrier construction, stronger in its unrestricted
internal syntax but explicitly NOT the annotation-to-operator bridge of the
whole printed carriers lemma. Captured ground slots are syntactically closed;
all remaining functional names share literal unit observations. -/
def ActualCarrier : Prop := ∀ (Γ : List Ty) (k r : Nat)
    (t : OriginalTerm (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1))),
  ∃ u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1)).level,
  ∃ w v : OrdinalVector (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) 1,
    assignment OrdinalSyntax.defaultPolicy t = some u ∧
    assignment OrdinalSyntax.defaultPolicy (saturate r (t.rename renameTracked)) = some w ∧
    assignment OrdinalSyntax.defaultPolicy (carrier t) = some v ∧
    v = GroundClosing.vector (groundMap _) w ∧
    v 0 = GroundClosing.expression (groundMap _) (w 0) ∧
    ∀ (ρ : Variable (Ty.curriedGround (k+1) :: Γ) .ground → Nat)
      (μ : Variable (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) .ground → Nat),
      expressionValue (UnitObservation.substitution μ) (v 1) =
        expressionValue (UnitObservation.substitution ρ) (u (headIndex r))
end LogicLineages.OrdinalComparison.Source.UnaryCarrier.Targets
