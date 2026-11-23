module

public import LogicLineages.NativeModule.PersistentMarking.NativeClosedApplication
public import LogicLineages.PersistentMarking.OrdinalRealizationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalRealizationTargets
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication OrdinalRealizationTargets

def nativeShape : FiniteType → SemanticType
  | .base => .base
  | .arrow A D => .arrow (nativeShape A) (nativeShape D)

def valueShape : SemanticType → FiniteType
  | .base => .base
  | .arrow A D => .arrow (valueShape A) (valueShape D)

def ExactSemanticShapes : Prop :=
  (∀ A, valueShape (nativeShape A) = A) ∧ (∀ A, nativeShape (valueShape A) = A)

def nativeTerms (S : Signature) : TermStructure where
  term := fun A => ClosedNativeTerm S (actualType (nativeShape A))
  below := fun _ t s => NativeBelow t s
  app := fun _ _ f u => applyClosed f u

def NativeRealizationClosure : Prop :=
  ExactSemanticShapes ∧ PointwiseSupremumExists ∧
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    RealizationStrictBackward (nativeTerms S) wf ∧
    RealizationDownward (nativeTerms S) wf ∧
    RealizationCountableSupremum (nativeTerms S) wf

def NativeLambdaRealization : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∀ (A D : FiniteType) (body : Expr)
      (hl : ClosedNative S (.lam (actualType (nativeShape A)) body)
        (.arrow (actualType (nativeShape A)) (actualType (nativeShape D))))
      (f : Value A → Value D),
      (∀ (x : Value A) (u : (nativeTerms S).term A), Realizes (nativeTerms S) wf A u x →
        ∃ v : (nativeTerms S).term D, v.val = substitute (.cons u.val .nil) 0 body ∧
          Realizes (nativeTerms S) wf D v (f x)) →
      Realizes (nativeTerms S) wf (.arrow A D) ⟨.lam (actualType (nativeShape A)) body, hl⟩ f

end LogicLineages.PersistentMarking.NativeOrdinalRealizationTargets
