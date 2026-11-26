import LogicLineages.PersistentMarking.BridgeTargets
import LogicLineages.PersistentMarking.SpineSubstitutionProof
namespace LogicLineages.PersistentMarking.OpeningFoundationProof
open Spine NameBridge

theorem prefixIndex (types : List Ty) (i : Nat) :
    BoundContext.«prefix» types EmptyContext i = types[i]? := by
  induction types generalizing i with
  | nil => rfl
  | cons σ types ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

mutual
 theorem typedScoped (types : List Ty) (q : Expr) (σ : Ty)
    (h : Typed (BoundContext.«prefix» types EmptyContext) q σ) : Scoped types q := by
  cases q with
  | free δ x => trivial
  | bound δ i =>
    cases h with
    | bound hi => simpa only [Scoped, prefixIndex] using hi
  | lam δ body =>
    cases h with
    | lam hb => exact typedScoped (δ::types) body _ hb
  | head f base =>
    cases h with
    | head hb => exact baseScoped types base _ hb
  | marked f τ base extras =>
    cases h with
    | marked hb he => exact ⟨baseScoped types base _ hb, extrasScoped types extras he⟩
 termination_by sizeOf q
 theorem baseScoped (types : List Ty) (qs : Args) (tys : List Ty)
    (h : BaseTyped (BoundContext.«prefix» types EmptyContext) qs tys) : ScopedArgs types qs := by
  cases qs with
  | nil => trivial
  | cons q qs =>
    cases h with
    | cons hq hqs => exact ⟨typedScoped types q _ hq, baseScoped types qs _ hqs⟩
 termination_by sizeOf qs
 theorem extrasScoped (types : List Ty) (qs : Args)
    (h : ExtrasTyped (BoundContext.«prefix» types EmptyContext) qs) : ScopedArgs types qs := by
  cases qs with
  | nil => trivial
  | cons q qs =>
    cases h with
    | cons hq hqs => exact ⟨typedScoped types q _ hq, extrasScoped types qs hqs⟩
 termination_by sizeOf qs
end

theorem typedClosedScoped : BridgeTargets.TypedClosedScoped := typedScoped []

theorem openingTyped : BridgeTargets.OpeningTyped := by
  intro σ τ body x hb
  exact SpineSubstitutionProof.parallelPreserves EmptyContext [σ]
    (.cons (.free σ x) .nil) body τ (.cons .free .nil) hb

mutual
 theorem aboveFresh (σ : Ty) (x : Nat) (q : Expr) (h : maxFreeName q < x) :
    freeOccurs (σ,x) q = false := by
  cases q with
  | free δ y =>
    have hn : (σ,x) ≠ (δ,y) := by
      intro he
      have hh := congrArg Prod.snd he
      simp only [maxFreeName] at h
      simp only at hh
      omega
    simp [freeOccurs, hn]
  | bound δ i => rfl
  | lam δ body => exact aboveFresh σ x body h
  | head f base => exact aboveFreshArgs σ x base h
  | marked f τ base extras =>
    have hb : maxFreeArgs base < x := by exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
    have he : maxFreeArgs extras < x := by exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
    simp only [freeOccurs, aboveFreshArgs σ x base hb, aboveFreshArgs σ x extras he, Bool.false_or]
 termination_by sizeOf q
 theorem aboveFreshArgs (σ : Ty) (x : Nat) (qs : Args) (h : maxFreeArgs qs < x) :
    freeOccursArgs (σ,x) qs = false := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hq : maxFreeName q < x := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
    have hqs : maxFreeArgs qs < x := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
    simp only [freeOccursArgs, aboveFresh σ x q hq, aboveFreshArgs σ x qs hqs, Bool.false_or]
 termination_by sizeOf qs
end

theorem freshOpeningExists : BridgeTargets.FreshOpeningExists := by
  intro σ s t
  let x := max (maxFreeName s) (maxFreeName t) + 1
  exact ⟨x, aboveFresh σ x s (by dsimp [x]; omega), aboveFresh σ x t (by dsimp [x]; omega)⟩
end LogicLineages.PersistentMarking.OpeningFoundationProof
