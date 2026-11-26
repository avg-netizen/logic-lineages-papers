import LogicLineages.PersistentMarking.FreeVariableApplicationProof
import LogicLineages.PersistentMarking.ElementarySupportProof
namespace LogicLineages.PersistentMarking.FreeVariableRelationSupport
open Spine NameBridge FreeVariableRawSupport

theorem atAbsent {qs : Args} {i : Nat} {q : Expr} (name : Name) (ha : At qs i q)
    (h : freeOccursArgs name qs = false) : freeOccurs name q = false := by
  induction ha with
  | here => exact (consParts h).1
  | there ha ih => exact ih (consParts h).2

theorem removeParts {xs rest : Args} {q : Expr} (name : Name) (hr : Remove xs q rest)
    (h : freeOccursArgs name xs = false) : freeOccurs name q = false ∧ freeOccursArgs name rest = false := by
  induction hr with
  | here => exact consParts h
  | there hr ih =>
    have hh := ih (consParts h).2
    exact ⟨hh.1,consAbsent (consParts h).1 hh.2⟩

theorem removeAbsent {xs rest : Args} {q : Expr} (name : Name) (hr : Remove xs q rest)
    (hq : freeOccurs name q = false) (hrest : freeOccursArgs name rest = false) : freeOccursArgs name xs = false := by
  induction hr with
  | here => exact consAbsent hq hrest
  | there hr ih => exact consAbsent (consParts hrest).1 (ih hq (consParts hrest).2)

theorem splitParts {xs ys zs : Args} (name : Name) (hs : Split xs ys zs)
    (h : freeOccursArgs name xs = false) : freeOccursArgs name ys = false ∧ freeOccursArgs name zs = false := by
  induction hs with
  | nil => exact ⟨rfl,rfl⟩
  | left hs ih => have hh := ih (consParts h).2; exact ⟨consAbsent (consParts h).1 hh.1,hh.2⟩
  | right hs ih => have hh := ih (consParts h).2; exact ⟨hh.1,consAbsent (consParts h).1 hh.2⟩

theorem splitAbsent {xs ys zs : Args} (name : Name) (hs : Split xs ys zs)
    (hy : freeOccursArgs name ys = false) (hz : freeOccursArgs name zs = false) : freeOccursArgs name xs = false := by
  induction hs with
  | nil => rfl
  | left hs ih => exact consAbsent (consParts hy).1 (ih (consParts hy).2 hz)
  | right hs ih => exact consAbsent (consParts hz).1 (ih hy (consParts hz).2)

theorem ownerCopiesAbsent (name : Name) (f : Head) (τ : Ty) (base extras : Args) (domains : List Ty)
    (h : freeOccurs name (.marked f τ base extras) = false) : freeOccursArgs name (ownerCopies f base extras domains) = false := by
  induction domains with
  | nil => rfl
  | cons σ ds ih => exact consAbsent (markedAbsent (markedParts h).1 (markedParts h).2) ih

theorem freshSingleton (name : Name) (σ : Ty) (x : Nat) (hn : name ≠ (σ,x)) :
    freeOccursArgs name (.cons (.free σ x) .nil) = false := by
  simp [freeOccursArgs,freeOccurs,hn]

theorem openingTarget (name : Name) (σ : Ty) (x : Nat) (s t : Expr)
    (hxt : freeOccurs (σ,x) t = false)
    (ih : ∀ name, freeOccurs name (openBody σ x s) = false → freeOccurs name (openBody σ x t) = false)
    (hs : freeOccurs name s = false) : freeOccurs name t = false := by
  by_cases he : name = (σ,x)
  · subst name; exact hxt
  · have hopen := substituteAbsent name (.cons (.free σ x) .nil) 0 s hs (freshSingleton name σ x he)
    exact substituteReflects name (.cons (.free σ x) .nil) 0 t (ih name hopen)
end LogicLineages.PersistentMarking.FreeVariableRelationSupport
