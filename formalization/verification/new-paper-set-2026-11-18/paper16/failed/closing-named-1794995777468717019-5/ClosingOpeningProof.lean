import LogicLineages.PersistentMarking.StructuralStabilityTargets
import LogicLineages.PersistentMarking.ClosedSyntaxProof
namespace LogicLineages.PersistentMarking.ClosingOpeningProof
open Spine NameBridge StructuralContext ClosedSyntaxProof

mutual
 theorem opening (name : Name) (y : Nat) (Γ : BoundContext) (d : Nat)
    (hb : Bounded Γ d) (q : Expr) (τ : Ty) (ht : Typed Γ q τ) :
    substitute (.cons (.free name.1 y) .nil) d (freeSub (closingMap name) d q) =
      freeSub (openingMap name y) d q := by
  cases q with
  | free σ x =>
    by_cases he : (σ,x) = name
    · subst name
      simp [freeSub,closingMap,openingMap,shift,substitute,Args.get]
    · simp [freeSub,closingMap,openingMap,he,shift,substitute]
  | bound σ i =>
    cases ht with
    | bound hi =>
      have hlt := hb i _ hi
      simp only [freeSub,substitute,hlt,if_true]
  | lam σ q =>
    cases ht with
    | lam hq => exact congrArg (Expr.lam σ) (opening name y (Γ.push σ) (d+1) (pushBound hb σ) q _ hq)
  | head f qs =>
    cases ht with
    | head hqs => exact congrArg (Expr.head f) (openingBases name y Γ d hb qs _ hqs)
  | marked f τ qs es =>
    cases ht with
    | marked hqs hes =>
      simp only [freeSub,substitute,openingBases name y Γ d hb qs _ hqs,
        openingExtras name y Γ d hb es hes]
 termination_by sizeOf q
 theorem openingBases (name : Name) (y : Nat) (Γ : BoundContext) (d : Nat)
    (hb : Bounded Γ d) (qs : Args) (types : List Ty) (ht : BaseTyped Γ qs types) :
    substituteArgs (.cons (.free name.1 y) .nil) d (freeSubArgs (closingMap name) d qs) =
      freeSubArgs (openingMap name y) d qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      simp only [freeSubArgs,substituteArgs,opening name y Γ d hb q _ hq,
        openingBases name y Γ d hb qs _ hqs]
 termination_by sizeOf qs
 theorem openingExtras (name : Name) (y : Nat) (Γ : BoundContext) (d : Nat)
    (hb : Bounded Γ d) (qs : Args) (ht : ExtrasTyped Γ qs) :
    substituteArgs (.cons (.free name.1 y) .nil) d (freeSubArgs (closingMap name) d qs) =
      freeSubArgs (openingMap name y) d qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      simp only [freeSubArgs,substituteArgs,opening name y Γ d hb q _ hq,
        openingExtras name y Γ d hb qs hqs]
 termination_by sizeOf qs
end

theorem closeOpen : StructuralStabilityTargets.CloseOpen := by
  intro name y q τ ht
  exact opening name y EmptyContext 0 emptyBound q τ ht
end LogicLineages.PersistentMarking.ClosingOpeningProof
