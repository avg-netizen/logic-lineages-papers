module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalMatrixLinearRowFormula (safeAtom safeAnd safeOr safePolarity safeTruth safeFalsity)
open PreparedProjection (LowerOperand PreparedInput)

theorem atomMapSafe (ops : List LowerOperand) (atom : NormalForm.Atom → NormalForm.Formula)
    (p : NormalForm.Formula) (safe : ∀ a ∈ LinearRows.atoms p, PreparedInput ops (atom a)) :
    PreparedInput ops (atomMap atom p) := by
  induction p with
  | truth => exact safeTruth ops
  | falsity => exact safeFalsity ops
  | atom a => exact safe a List.mem_cons_self
  | negative p ih => exact safePolarity ops _ (ih safe) false
  | conjunction p q hp hq =>
      exact safeAnd ops _ _ (hp (fun a ha => safe a (List.mem_append_left _ ha)))
        (hq (fun a ha => safe a (List.mem_append_right _ ha)))
  | disjunction p q hp hq =>
      exact safeOr ops _ _ (hp (fun a ha => safe a (List.mem_append_left _ ha)))
        (hq (fun a ha => safe a (List.mem_append_right _ ha)))

theorem atomMapMeaning (atom : NormalForm.Atom → NormalForm.Formula)
    (p : NormalForm.Formula) (ν θ : Nat → Nat)
    (meaning : ∀ a ∈ LinearRows.atoms p, (atom a).eval ν ↔ a.eval θ) :
    (atomMap atom p).eval ν ↔ p.eval θ := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact meaning a List.mem_cons_self
  | negative p ih => exact not_congr (ih meaning)
  | conjunction p q hp hq =>
      exact and_congr (hp (fun a ha => meaning a (List.mem_append_left _ ha)))
        (hq (fun a ha => meaning a (List.mem_append_right _ ha)))
  | disjunction p q hp hq =>
      exact or_congr (hp (fun a ha => meaning a (List.mem_append_left _ ha)))
        (hq (fun a ha => meaning a (List.mem_append_right _ ha)))

theorem conjoinSafe (ops : List LowerOperand) (ps : List NormalForm.Formula)
    (safe : ∀ q ∈ ps, PreparedInput ops q) : PreparedInput ops (conjoin ps) := by
  induction ps with
  | nil => exact safeTruth ops
  | cons p ps ih =>
      exact safeAnd ops _ _ (safe p List.mem_cons_self)
        (ih (fun q hq => safe q (List.mem_cons_of_mem _ hq)))

theorem conjoinMeaning (ν : Nat → Nat) (ps : List NormalForm.Formula) :
    (conjoin ps).eval ν ↔ ∀ q ∈ ps, q.eval ν := by
  induction ps with
  | nil => simp [conjoin,NormalForm.Formula.eval]
  | cons p ps ih =>
      change (p.eval ν ∧ (conjoin ps).eval ν) ↔ _
      rw [ih]
      constructor
      · rintro ⟨head,tail⟩ q member
        rcases List.mem_cons.mp member with rfl | later
        · exact head
        · exact tail q later
      · intro h
        exact ⟨h p List.mem_cons_self,fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

theorem lowerSafe (ops : List LowerOperand) (n : Nat) : PreparedInput ops (lowerBound n) := by
  apply safeAtom
  · intro t h
    obtain rfl := List.mem_singleton.mp h
    exact ⟨0,rfl⟩
  · intro i hi
    have eq : i = 0 := List.mem_singleton.mp hi
    subst i
    exact Nat.zero_le _

theorem lowerMeaning (n : Nat) (ν : Nat → Nat) : (lowerBound n).eval ν ↔ n ≤ ν 0 := by
  change 0 ≤ -(n : Int) + (1 * (ν 0 : Int) + 0) ↔ _
  simp only [one_mul,add_zero]
  omega

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
