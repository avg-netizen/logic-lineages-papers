module
public import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceTargets
import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceReadProof
import LogicLineages.PermittedControl.SharedRankResidueRowCellProof
import LogicLineages.PermittedControl.MixedRankResidueCodeProof
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixPaidCongruence
open MixedSameRankResidue (WeightedOperand orderedReads actualSum properOperand)
open PreparedProjection (LowerOperand LowerOperandActual)
open SignedRowSliceValue (valueAt)

private theorem properRead (f ρ : Nat → Nat) (op : LowerOperand) (v : Nat)
    (actual : LowerOperandActual f ρ op v) : properOperand op := by
  cases op with
  | coordinate _ => trivial
  | ordinary _ F =>
      cases F with
      | iterate _ => trivial
      | entry k lam mu => exact actual.1.1
  | count _ _ _ => exact actual.1.1

private theorem allProper (f ρ : Nat → Nat) (ts : List WeightedOperand) (vs : List Nat)
    (reads : orderedReads f ρ ts vs) : ∀ t ∈ ts, properOperand t.2 := by
  induction ts generalizing vs with
  | nil =>
      intro t h
      cases h
  | cons u ts ih =>
      cases vs with
      | nil => exact False.elim reads
      | cons v vs =>
          intro t member
          rcases List.mem_cons.mp member with eq | rest
          · subst t
            exact properRead f ρ u.2 v reads.1
          · exact ih vs reads.2.2 t rest

private theorem uniqueReads (f ρ : Nat → Nat) (ts : List WeightedOperand) (vs ws : List Nat)
    (a : orderedReads f ρ ts vs) (b : orderedReads f ρ ts ws) : vs = ws := by
  induction ts generalizing vs ws with
  | nil =>
      cases vs with
      | cons v vs => exact False.elim a
      | nil => cases ws with
        | nil => rfl
        | cons w ws => exact False.elim b
  | cons t ts ih =>
      cases vs with
      | nil => exact False.elim a
      | cons v vs =>
          cases ws with
          | nil => exact False.elim b
          | cons w ws =>
              have head : v = w := Option.some.inj (Option.some.inj (a.2.1.symm.trans b.2.1))
              have rest := ih vs ws a.2.2 b.2.2
              rw [head,rest]

theorem exactPaidCongruenceAtValue : ExactPaidCongruenceAtValue := by
  intro f B hf ρ ν layout m c ts v positive covered paid tie actual
  obtain ⟨values,source,eq⟩ := actual
  obtain ⟨ws,independent,cong⟩ :=
    exactPaidCongruenceReads f B hf ρ layout m c ts positive covered
      (allProper f ρ ts values source) paid
  have same := uniqueReads f ρ ts ws values independent source
  rw [same,eq] at cong
  have formula := SharedRankResidueRow.formulaAt layout (m,c,ts) ρ ν positive tie
  change (modular layout m c ts).eval ν ↔ _
  refine formula.trans ?_
  unfold digitResult at cong
  rw [MixedRankResidue.codeExact.2.2.2 ts] at cong
  exact cong.dvd_iff.symm

end LogicLineages.PermittedControl.OriginalMatrixPaidCongruence
