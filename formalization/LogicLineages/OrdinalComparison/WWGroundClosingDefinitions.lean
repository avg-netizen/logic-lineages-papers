module
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundClosing

/-- A typed name survives, or a ground name becomes literal source zero.
Functional names cannot be replaced by a fictitious unit inhabitant. -/
inductive Image (Δ : List Ty) : Ty → Type where
  | var {σ : Ty} : Variable Δ σ → Image Δ σ
  | zero : Image Δ .ground

abbrev GroundMap (Γ Δ : List Ty) := ∀ {σ : Ty}, Variable Γ σ → Image Δ σ

def Image.weaken {Δ σ τ} : Image Δ σ → Image (τ :: Δ) σ
  | .var x => .var (.there x)
  | .zero => .zero

def GroundMap.lift {Γ Δ τ} (r : GroundMap Γ Δ) : GroundMap (τ :: Γ) (τ :: Δ)
  | _, .here => .var .here
  | _, .there x => (r x).weaken

def Image.source {Δ σ} : Image Δ σ → OriginalTerm Δ σ
  | .var x => .var x
  | .zero => .zeroC

def GroundMap.source {Γ Δ} (r : GroundMap Γ Δ) :=
  fun {σ} (x : Variable Γ σ) => (r x).source

def component {Γ Δ} (r : GroundMap Γ Δ) : OrdinalComponent Γ → OrdinalExpression Δ
  | ⟨_, x, j⟩ => match r x with
    | .var y => .var ⟨_, y, j⟩
    | .zero => .one

def expression {Γ Δ} (r : GroundMap Γ Δ) : OrdinalExpression Γ → OrdinalExpression Δ :=
  LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.substitute (component r)

def vector {Γ Δ} (r : GroundMap Γ Δ) {m : Nat} (v : OrdinalVector Γ m) : OrdinalVector Δ m :=
  fun j => expression r (v j)

def partialVector {Γ Δ} (r : GroundMap Γ Δ) {σ : Ty}
    (v : OrdinalPartialVector Γ σ) : OrdinalPartialVector Δ σ :=
  fun j => expression r (v j)
end LogicLineages.OrdinalComparison.Source.GroundClosing
