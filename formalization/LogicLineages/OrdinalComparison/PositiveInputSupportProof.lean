module
public import LogicLineages.OrdinalComparison.PositiveInputSupportTargets
public import LogicLineages.OrdinalComparison.EncodedCollapseProof
public import LogicLineages.OrdinalComparison.ProfileHeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem positive_head_program (rho : NONote) (n : Nat) :
    actualProfileHead rho n ∈ encodedCollapsePartial (rawNoteEncode (finiteTail rho n).1) := by
  classical
  let r := finiteTail rho n
  have hd := encodedCollapseTotal (rawNoteEncode r.1)
  have hm : encodedCollapseValue (rawNoteEncode r.1) ∈ encodedCollapsePartial (rawNoteEncode r.1) := by
    unfold encodedCollapseValue
    rw [Part.getOrElse_of_dom _ hd 0]
    exact Part.get_mem hd
  rw [encodedCollapseSourceCorrect r] at hm
  have hr : r.1.repr=rho.1.repr+(n : Ordinal) := (finiteTailCorrect rho n).1
  rw [hr] at hm
  exact hm

theorem positiveClosedProgramCorrect : Targets.PositiveClosedProgramCorrect := by
  intro E
  induction E with
  | constant n => exact Part.mem_some _
  | input => exact Part.mem_some _
  | add E F ihE ihF => exact Part.mem_bind ihE (Part.mem_map (fun b => actualFixedLimitProfileEval E 0+b) ihF)
  | head rho E ih => exact Part.mem_bind ih (positive_head_program rho (actualFixedLimitProfileEval E 0))

theorem positiveClosedProgramTotal : Targets.PositiveClosedProgramTotal :=
  fun E => (positiveClosedProgramCorrect E).1

theorem positiveInputAbsent : Targets.PositiveInputAbsent := by
  intro E
  induction E with
  | constant n => intro _ x; rfl
  | input => intro h; cases h
  | add E F ihE ihF =>
    intro h x
    have hs : positiveExprHasInput E=false ∧ positiveExprHasInput F=false := by
      simpa only [positiveExprHasInput,Bool.or_eq_false_iff] using h
    exact congrArg₂ (·+·) (ihE hs.1 x) (ihF hs.2 x)
  | head rho E ih =>
    intro h x
    exact congrArg (actualProfileHead rho) (ih h x)

theorem positiveInputPresentLower : Targets.PositiveInputPresentLower := by
  intro E
  induction E with
  | constant n => intro _ h; cases h
  | input => intro _ _ x; exact le_rfl
  | add E F ihE ihF =>
    intro hv h x
    have hs : positiveExprHasInput E=true ∨ positiveExprHasInput F=true := by
      simpa only [positiveExprHasInput,Bool.or_eq_true] using h
    rcases hs with hE | hF
    · exact (ihE hv.1 hE x).trans (Nat.le_add_right _ _)
    · exact (ihF hv.2 hF x).trans (Nat.le_add_left _ _)
  | head rho E ih =>
    intro hv h x
    exact (ih hv.2.2 h x).trans ((actualFixedLimitProfileHeads rho hv.1).2 _).le

end LogicLineages.OrdinalComparison
