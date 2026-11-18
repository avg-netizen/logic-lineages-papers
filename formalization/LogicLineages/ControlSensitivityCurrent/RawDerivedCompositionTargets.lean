module
public import LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
open RawSourceDAG RawSourceDAG.CheckedComposition RawSourceDAG.DerivedComposition

def TypedExactness : Prop :=
  (∀ (Γ : List Ty) (a b : Input Γ .ground),
    detectors (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) = some
      (encode ⟨Γ,.ground,ScopedDAG.detectorLeft a b⟩,encode ⟨Γ,.ground,ScopedDAG.detectorRight a b⟩)) ∧
  (∀ (Γ : List Ty) (es : List (Input Γ .ground × Input Γ .ground)),
    DerivedComposition.aggregate (Γ.map SyntaxCode.typeCode)
      (es.map (fun p => (encode ⟨Γ,.ground,p.1⟩,encode ⟨Γ,.ground,p.2⟩))) = some
        (encode ⟨Γ,.ground,(ScopedDAG.aggregate es).1⟩,encode ⟨Γ,.ground,(ScopedDAG.aggregate es).2⟩)) ∧
  ∀ (Γ : List Ty) (a : Input Γ .ground) (upper : Bool),
    wrap upper (encode ⟨Γ,.ground,a⟩) = some
      (encode ⟨Γ,.ground,if upper then upperInput a else lowerInput a⟩)

def SuccessReconstruction : Prop :=
  (∀ (ca cb : Code) (out : Code × Code), detectors ca cb=some out →
    ∃ (Γ : List Ty) (a b : Input Γ .ground),
      encode ⟨Γ,.ground,a⟩=ca ∧ encode ⟨Γ,.ground,b⟩=cb ∧
      out=(encode ⟨Γ,.ground,ScopedDAG.detectorLeft a b⟩,encode ⟨Γ,.ground,ScopedDAG.detectorRight a b⟩) ∧
      decode out.1=some ⟨Γ,.ground,ScopedDAG.detectorLeft a b⟩ ∧
      decode out.2=some ⟨Γ,.ground,ScopedDAG.detectorRight a b⟩) ∧
  (∀ (context : List Nat) (raw : List (Code × Code)) (out : Code × Code),
    DerivedComposition.aggregate context raw=some out →
    ∃ (Γ : List Ty) (es : List (Input Γ .ground × Input Γ .ground)),
      Γ.map SyntaxCode.typeCode=context ∧
      es.map (fun p => (encode ⟨Γ,.ground,p.1⟩,encode ⟨Γ,.ground,p.2⟩))=raw ∧
      out=(encode ⟨Γ,.ground,(ScopedDAG.aggregate es).1⟩,encode ⟨Γ,.ground,(ScopedDAG.aggregate es).2⟩) ∧
      decode out.1=some ⟨Γ,.ground,(ScopedDAG.aggregate es).1⟩ ∧
      decode out.2=some ⟨Γ,.ground,(ScopedDAG.aggregate es).2⟩) ∧
  ∀ (upper : Bool) (c out : Code), wrap upper c=some out →
    ∃ (Γ : List Ty) (a : Input Γ .ground), encode ⟨Γ,.ground,a⟩=c ∧
      out=encode ⟨Γ,.ground,if upper then upperInput a else lowerInput a⟩ ∧
      decode out=some ⟨Γ,.ground,if upper then upperInput a else lowerInput a⟩

def RejectionAndCounts : Prop :=
  (∀ a b : Code, detectors a b=none ↔ eraserGuard a b=false) ∧
  (∀ (context : List Nat) (es : List (Code × Code)),
    DerivedComposition.aggregate context es=none ↔ aggregateGuard context es=false) ∧
  (∀ (upper : Bool) (c : Code), wrap upper c=none ↔ wrapperGuard c=false) ∧
  (∀ a b : Code,
    (detectorLeftRaw a b).2.1.length=2*(a.2.1.length+b.2.1.length)+6 ∧
    (detectorRightRaw a b).2.1.length=2*(a.2.1.length+b.2.1.length)+6) ∧
  (∀ (context : List Nat) (es : List (Code × Code)),
    (aggregateRaw context es).1.2.1.length=rawWeight es ∧
    (aggregateRaw context es).2.2.1.length=rawWeight es) ∧
  (∀ (upper : Bool) (c : Code), (wrapperRaw upper c).2.1.length=c.2.1.length+6) ∧
  (∀ (a b : Code) (out : Code × Code), detectors a b=some out → valid out.1=true ∧ valid out.2=true) ∧
  (∀ (context : List Nat) (es : List (Code × Code)) (out : Code × Code),
    DerivedComposition.aggregate context es=some out → valid out.1=true ∧ valid out.2=true) ∧
  ∀ (upper : Bool) (c out : Code), wrap upper c=some out → valid out=true

def Effective : Prop :=
  Computable (fun p : Code × Code => detectors p.1 p.2) ∧
  Computable (fun p : List Nat × List (Code × Code) => DerivedComposition.aggregate p.1 p.2) ∧
  Computable (fun p : Bool × Code => wrap p.1 p.2)
end LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionTargets
