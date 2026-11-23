module

public import LogicLineages.NativeModule.PersistentMarking.StructuralStabilityTargets
public import LogicLineages.NativeModule.PersistentMarking.FreeTypingProof
public import LogicLineages.NativeModule.PersistentMarking.SubstitutionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ClosingProof
open Spine NameBridge StructuralContext

theorem weakening (q : Expr) (τ : Ty) (h : Typed EmptyContext q τ) (Γ : BoundContext) :
    Typed Γ q τ := by
  have hc : ShiftCompatible 0 0 EmptyContext Γ := by
    intro i σ hi
    simp [EmptyContext] at hi
  have hh := SpineShiftProof.shiftPreserves EmptyContext Γ q τ 0 0 h hc
  simpa only [SubstitutionProof.shiftZero] using hh

theorem closingTyped (name : Name) : FreeMapTyped (EmptyContext.push name.1) (closingMap name) := by
  intro σ x
  by_cases he : (σ,x) = name
  · subst name
    simp only [closingMap, if_true]
    exact .bound rfl
  · simp only [closingMap,he,if_false]
    exact .free

theorem closeTyped : StructuralStabilityTargets.CloseTyped := by
  intro name q τ ht
  exact FreeTypingProof.freeSubTyped _ _ (closingTyped name) _ _
    (weakening q τ ht (EmptyContext.push name.1))

mutual
 theorem validity (S : Signature) (name : Name) (d : Nat) (q : Expr) (h : Valid S q) :
    Valid S (freeSub (closingMap name) d q) := by
  cases q with
  | free σ x =>
    by_cases he : (σ,x) = name <;> simp [freeSub,closingMap,he,shift,Valid]
  | bound σ i => trivial
  | lam σ q => exact validity S name (d+1) q h
  | head f qs => exact ⟨h.1,validityArgs S name d qs h.2⟩
  | marked f τ qs es => exact ⟨h.1,validityArgs S name d qs h.2.1,validityArgs S name d es h.2.2⟩
 termination_by sizeOf q
 theorem validityArgs (S : Signature) (name : Name) (d : Nat) (qs : Args) (h : ValidArgs S qs) :
    ValidArgs S (freeSubArgs (closingMap name) d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨validity S name d q h.1,validityArgs S name d qs h.2⟩
 termination_by sizeOf qs
end

mutual
 theorem ordinary (name : Name) (d : Nat) (q : Expr) (h : Ordinary q) :
    Ordinary (freeSub (closingMap name) d q) := by
  cases q with
  | free σ x =>
    by_cases he : (σ,x) = name <;> simp [freeSub,closingMap,he,shift,Ordinary]
  | bound σ i => trivial
  | lam σ q => exact ordinary name (d+1) q h
  | head f qs => exact ordinaryArgs name d qs h
  | marked f τ qs es => exact h.elim
 termination_by sizeOf q
 theorem ordinaryArgs (name : Name) (d : Nat) (qs : Args) (h : OrdinaryArgs qs) :
    OrdinaryArgs (freeSubArgs (closingMap name) d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨ordinary name d q h.1,ordinaryArgs name d qs h.2⟩
 termination_by sizeOf qs
end

mutual
 theorem absence (name other : Name) (d : Nat) (q : Expr) (h : freeOccurs other q = false) :
    freeOccurs other (freeSub (closingMap name) d q) = false := by
  cases q with
  | free σ x =>
    by_cases he : (σ,x) = name
    · simp [freeSub,closingMap,he,shift,freeOccurs]
    · simpa only [freeSub,closingMap,he,if_false,shift] using h
  | bound σ i => rfl
  | lam σ q => exact absence name other (d+1) q h
  | head f qs => exact absenceArgs name other d qs h
  | marked f τ qs es =>
    have hp := Bool.or_eq_false_iff.mp h
    simp only [freeSub,freeOccurs,absenceArgs name other d qs hp.1,
      absenceArgs name other d es hp.2,Bool.false_or]
 termination_by sizeOf q
 theorem absenceArgs (name other : Name) (d : Nat) (qs : Args) (h : freeOccursArgs other qs = false) :
    freeOccursArgs other (freeSubArgs (closingMap name) d qs) = false := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hp := Bool.or_eq_false_iff.mp h
    simp only [freeSubArgs,freeOccursArgs,absence name other d q hp.1,
      absenceArgs name other d qs hp.2,Bool.false_or]
 termination_by sizeOf qs
end

theorem closeValidity : StructuralStabilityTargets.CloseValidity := fun S name q h => validity S name 0 q h
theorem closeOrdinary : StructuralStabilityTargets.CloseOrdinary := fun name q h => ordinary name 0 q h
theorem closeAbsence : StructuralStabilityTargets.CloseAbsence := fun name other q h => absence name other 0 q h
end LogicLineages.PersistentMarking.ClosingProof
