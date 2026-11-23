module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalRealizationTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeIteratorChecks
public import LogicLineages.NativeModule.PersistentMarking.NativeIndexedCarrierSubtype
public import LogicLineages.PersistentMarking.OrdinalNativeIterationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalIterationTargets
open Spine NativeIndexedCarrierTargets NativeIteratorTargets NativeIteratorStrictTargets
open NativeIndexedCarrierSubtype NativeOrdinalRealizationTargets
open OrdinalRealizationTargets OrdinalNativeIterationTargets

def iteratorShape (A : FiniteType) : FiniteType := .arrow .base (.arrow (.arrow A A) (.arrow A A))

def typedIterator (S : Signature) (A : FiniteType) : (nativeTerms S).term (iteratorShape A) :=
  ⟨iterator (nativeShape A), NativeIteratorChecks.exact_ClosedNativeIterator S (nativeShape A)⟩

def NativeIndexedCarrierOrbit : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    IndexedCarrierRealizesOrbit (nativeTerms S) wf (fun A => indexedTerm (nativeShape A))

def NativeIteratorRealizesFullPrefix : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∀ A, ∃ iterate : Value (iteratorShape A),
      (∀ f x, OrbitEquations A f x (fun α => iterate α f x)) ∧
      Realizes (nativeTerms S) wf (iteratorShape A) (typedIterator S A) iterate

end LogicLineages.PersistentMarking.NativeOrdinalIterationTargets
