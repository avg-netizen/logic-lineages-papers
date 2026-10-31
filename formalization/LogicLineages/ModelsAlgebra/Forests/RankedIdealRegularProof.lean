module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegular.Proof
open RankedParse ProfileAutomatonEncoding RankedIdealContext RankedIdealConstructors

theorem runCalibration : Targets.RunCalibration := by
  intro M n rules t
  induction t with
  | atom => rfl
  | node o l r ihl ihr =>
      change (starMachine M rules).node o (machineRun (starMachine M rules) l)
        (machineRun (starMachine M rules) r) = _
      rw [ihl, ihr]
      rfl

private theorem base_flag (M : Machine) {n} (rules : Fin n → Rule) t
    (h : language M t) : flag M rules t = true := by
  cases t with
  | atom => exact h
  | node o l r => exact Bool.or_eq_true_iff.mpr (Or.inl h)

private theorem flag_sound (M : Machine) {n} (rules : Fin n → Rule) t :
    flag M rules t = true → Star (allowed rules) (language M) t := by
  induction t with
  | atom => intro h; exact .base h
  | node o l r ihl ihr =>
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact .base h
      · obtain ⟨i, ho, hi⟩ := of_decide_eq_true h
        subst o
        cases hc : (rules i).holeLeft with
        | false =>
            simp only [hc, Bool.false_eq_true, if_false] at hi
            have ha : allowed rules (.right (rules i).op l .hole) :=
              ⟨i, l, hi.1, by simp [hc]⟩
            exact .step ha (ihr hi.2)
        | true =>
            simp only [hc, if_true] at hi
            have ha : allowed rules (.left (rules i).op .hole r) :=
              ⟨i, r, hi.2, by simp [hc]⟩
            exact .step ha (ihl hi.1)

private theorem flag_complete (M : Machine) {n} (rules : Fin n → Rule) t
    (h : Star (allowed rules) (language M) t) : flag M rules t = true := by
  induction h with
  | base h => exact base_flag M rules _ h
  | @step c t hc ht ih =>
      obtain ⟨i, u, hu, rfl⟩ := hc
      cases hb : (rules i).holeLeft with
      | false =>
          simp only [hb, Bool.false_eq_true, if_false, plug]
          apply Bool.or_eq_true_iff.mpr
          right
          apply decide_eq_true
          exact ⟨i, rfl, by simpa [hb, language] using And.intro hu ih⟩
      | true =>
          simp only [hb, if_true, plug]
          apply Bool.or_eq_true_iff.mpr
          right
          apply decide_eq_true
          exact ⟨i, rfl, by simpa [hb, language] using And.intro ih hu⟩

theorem starExact : Targets.StarExact := by
  intro M n rules t
  change (machineRun (starMachine M rules) t).2.2 = true ↔ _
  rw [runCalibration M n rules t]
  exact ⟨flag_sound M rules t, flag_complete M rules t⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegular.Proof
