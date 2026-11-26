import LogicLineages.PersistentMarking.Comparison
namespace LogicLineages.PersistentMarking.FreeVariableTargets
open Spine NameBridge

def SubstitutePreservesAbsence : Prop := ∀ name values depth q,
  freeOccurs name q = false → freeOccursArgs name values = false →
  freeOccurs name (substitute values depth q) = false

def SubstituteReflectsAbsence : Prop := ∀ name values depth q,
  freeOccurs name (substitute values depth q) = false → freeOccurs name q = false

def SuccessfulApplicationAbsence : Prop := ∀ name q args r,
  freeOccurs name q = false → freeOccursArgs name args = false →
  apply q args = some r → freeOccurs name r = false

def WeakContainment : Prop := ∀ S s t, Weak S s t →
  ∀ name, freeOccurs name t = true → freeOccurs name s = true

def StrictContainment : Prop := ∀ S s t, Strict S s t →
  ∀ name, freeOccurs name t = true → freeOccurs name s = true

def FullContainment : Prop := WeakContainment ∧ StrictContainment
end LogicLineages.PersistentMarking.FreeVariableTargets
