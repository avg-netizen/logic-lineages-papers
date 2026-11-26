module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
open RawSourceDAG RawSourceDAG.CheckedComposition

def TypedExactness : Prop :=
  (∀ (Γ : List Ty) (σ τ : Ty) (f : Input Γ (.arrow σ τ)) (a : Input Γ σ),
    CheckedComposition.application (SyntaxCode.typeCode τ) (encode ⟨Γ,.arrow σ τ,f⟩) (encode ⟨Γ,σ,a⟩) =
      some (encode ⟨Γ,τ,ScopedDAG.application f a⟩)) ∧
  ∀ (Γ : List Ty) (a b : Input Γ .ground),
    CheckedComposition.eraser (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) =
      some (encode ⟨Γ,.ground,ScopedDAG.eraser a b⟩)

def SuccessReconstruction : Prop :=
  (∀ (t : Nat) (cf ca co : Code), CheckedComposition.application t cf ca = some co →
    ∃ (Γ : List Ty) (σ τ : Ty) (f : Input Γ (.arrow σ τ)) (a : Input Γ σ),
      SyntaxCode.typeCode τ=t ∧ encode ⟨Γ,.arrow σ τ,f⟩=cf ∧ encode ⟨Γ,σ,a⟩=ca ∧
      encode ⟨Γ,τ,ScopedDAG.application f a⟩=co ∧
      decode co=some ⟨Γ,τ,ScopedDAG.application f a⟩) ∧
  ∀ (ca cb co : Code), CheckedComposition.eraser ca cb = some co →
    ∃ (Γ : List Ty) (a b : Input Γ .ground),
      encode ⟨Γ,.ground,a⟩=ca ∧ encode ⟨Γ,.ground,b⟩=cb ∧
      encode ⟨Γ,.ground,ScopedDAG.eraser a b⟩=co ∧
      decode co=some ⟨Γ,.ground,ScopedDAG.eraser a b⟩

def RejectionAndCounts : Prop :=
  (∀ (t : Nat) (f a : Code), CheckedComposition.application t f a=none ↔ applicationGuard t f a=false) ∧
  (∀ (a b : Code), CheckedComposition.eraser a b=none ↔ eraserGuard a b=false) ∧
  (∀ (t : Nat) (f a : Code), (applicationRaw t f a).2.1.length=f.2.1.length+a.2.1.length+1) ∧
  (∀ (a b : Code), (eraserRaw a b).2.1.length=a.2.1.length+b.2.1.length+2) ∧
  (∀ (t : Nat) (f a co : Code), CheckedComposition.application t f a=some co →
    valid co=true ∧ co.1=f.1 ∧ co.2.2.1=0 ∧ co.2.2.2=t ∧
    co.2.1.length=f.2.1.length+a.2.1.length+1) ∧
  ∀ (a b co : Code), CheckedComposition.eraser a b=some co →
    valid co=true ∧ co.1=a.1 ∧ co.2.2.1=0 ∧ co.2.2.2=0 ∧
    co.2.1.length=a.2.1.length+b.2.1.length+2

def Effective : Prop :=
  Computable (fun p : Nat × Code × Code => CheckedComposition.application p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Code × Code => CheckedComposition.eraser p.1 p.2)
end LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionTargets
