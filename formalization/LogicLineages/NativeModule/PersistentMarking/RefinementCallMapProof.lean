module

public import LogicLineages.NativeModule.PersistentMarking.RefinementSubstitutionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementCallMapProof
open Spine NameBridge

def replace (σ : Ty) (x : Nat) (a : Expr) : FreeMap := fun τ y => if (τ,y)=(σ,x) then a else .free τ y

theorem typed (σ : Ty) (x : Nat) (a : Expr) (h : Typed EmptyContext a σ) : FreeMapTyped EmptyContext (replace σ x a) := by
  intro τ y
  by_cases he : (τ,y)=(σ,x)
  · have ht : τ=σ := congrArg Prod.fst he
    subst τ
    simpa only [replace,he,if_true] using h
  · simp only [replace,he,if_false]
    exact .free

theorem related (S : Signature) (σ : Ty) (x : Nat) (a b : Expr) (h : Refines S a b) :
    ∀ τ y, Refines S (replace σ x a τ y) (replace σ x b τ y) := by
  intro τ y
  by_cases he : (τ,y)=(σ,x)
  · simpa only [replace,he,if_true] using h
  · simp only [replace,he,if_false]; exact ⟨.var⟩

mutual
 theorem absent (σ : Ty) (x : Nat) (a : Expr) (d : Nat) (q : Expr) (h : freeOccurs (σ,x) q = false) :
    freeSub (replace σ x a) d q = q := by
  cases q with
  | free τ y =>
    have hn : (σ,x) ≠ (τ,y) := by simpa only [freeOccurs,decide_eq_false_iff_not] using h
    have hn' : (τ,y) ≠ (σ,x) := fun he => hn he.symm
    simp only [freeSub,replace,hn',if_false,shift]
  | bound τ i => rfl
  | lam τ q => exact congrArg (Expr.lam τ) (absent σ x a (d+1) q h)
  | head f qs => exact congrArg (Expr.head f) (absentArgs σ x a d qs h)
  | marked f τ qs es =>
    have hh : freeOccursArgs (σ,x) qs = false ∧ freeOccursArgs (σ,x) es = false := by simpa only [freeOccurs,Bool.or_eq_false_iff] using h
    change Expr.marked f τ _ _ = Expr.marked f τ _ _
    exact congr (congrArg (Expr.marked f τ) (absentArgs σ x a d qs hh.1)) (absentArgs σ x a d es hh.2)
 termination_by sizeOf q
 theorem absentArgs (σ : Ty) (x : Nat) (a : Expr) (d : Nat) (qs : Args) (h : freeOccursArgs (σ,x) qs = false) :
    freeSubArgs (replace σ x a) d qs = qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hh : freeOccurs (σ,x) q = false ∧ freeOccursArgs (σ,x) qs = false := by simpa only [freeOccursArgs,Bool.or_eq_false_iff] using h
    change Args.cons _ _ = Args.cons _ _
    exact congr (congrArg Args.cons (absent σ x a d q hh.1)) (absentArgs σ x a d qs hh.2)
 termination_by sizeOf qs
end

theorem realize (σ : Ty) (x : Nat) (a : Expr) (qs : Args) (h : freeOccursArgs (σ,x) qs = false) :
    freeSubArgs (replace σ x a) 0 (.cons (.free σ x) qs) = .cons a qs := by
  simp only [freeSubArgs,freeSub,replace,ite_true,SubstitutionProof.shiftZero,absentArgs σ x a 0 qs h]
end LogicLineages.PersistentMarking.RefinementCallMapProof
