module
public import LogicLineages.PermittedControl.ActualGreatestCongruenceRouteTargets
import LogicLineages.PermittedControl.ActualGreatestCongruenceRouteLayoutProof
import LogicLineages.PermittedControl.SharedRankResidueRowSupportProof
import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceValueProof
import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceReadProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGreatestCongruenceRoute
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand encodeWeighted weightedTailCode actualSum)
open OriginalMatrixPaidCongruence (modular paidTerms exactPaidCongruenceAtValue exactPaidCongruenceReads)
open OriginalMatrixLinearRowFormula (choosePolarity safePolarity)
open ActualSymbolicZeroSuccessor (SyntaxState)
open SignedRowGuardedTest (Test)
open SignedRowSliceValue (valueAt)

theorem exactGreatestCongruenceShape : ExactGreatestCongruenceShape := by
  intro top m s positive
  let ls := layout top s.terms
  have shape := SharedRankResidueRow.formulaSupport ls (m,s.constant,s.terms)
  have bounds : ∀ n ∈ (modular ls m s.constant s.terms).variables, n ≤ (table top s.terms).length := by
    intro n used
    obtain ⟨req,member,eq⟩ := List.mem_map.mp (shape.2 n used)
    obtain ⟨slot,slotMember,what⟩ := List.mem_map.mp member
    have nameEq : slot.1 = n := by
      rw [← eq,← what]
    rw [← nameEq]
    exact (exactGreatestResidueLayout top s.terms).2.2 slot slotMember
  exact safePolarity (table top s.terms) _ ⟨shape.1,bounds⟩ positive

private theorem tailDomination (B m : Nat) (s : SyntaxState) :
    ∀ t ∈ s.terms, weightedTailCode B m [encodeWeighted t] ≤ modulusMinimum B m s := by
  cases s with
  | mk c terms =>
    induction terms with
    | nil => intro t used; cases used
    | cons a ts ih =>
      intro t used
      change weightedTailCode B m [encodeWeighted t] ≤
        max (weightedTailCode B m [encodeWeighted a]) (modulusMinimum B m ⟨c,ts⟩)
      rcases List.mem_cons.mp used with head | rest
      · subst t; exact le_max_left _ _
      · exact (ih t rest).trans (le_max_right _ _)

private theorem polarityIff (m : Nat) (v : Int) (p : NormalForm.Formula) (ν : Nat → Nat)
    (positive : Bool) (h : p.eval ν ↔ (m : Int) ∣ v) :
    (choosePolarity p positive).eval ν ↔ (Test.congruence m).atPolarity positive v := by
  cases positive with
  | false => exact not_congr h
  | true => exact h

theorem exactGreatestCongruencePacket : ExactGreatestCongruencePacket := by
  intro f B selected baseline top m s setup z minimum positive
  let θ := Function.update baseline top z
  let ls := layout top s.terms
  let p := modular ls m s.constant s.terms
  let q := packet top m s positive
  have covers := (exactGreatestResidueLayout top s.terms).1 (fun t used => (setup.2.1 t used).1)
  have paid : paidTerms B m θ s.terms := by
    intro t used
    have common : modulusMinimum B m s ≤ θ t.2.rank := by
      rcases lt_or_eq_of_le (setup.2.1 t used).1 with small | large
      · change modulusMinimum B m s ≤ Function.update baseline top z t.2.rank
        rw [Function.update_of_ne (ne_of_lt small)]
        exact setup.2.2 t used small
      · change modulusMinimum B m s ≤ Function.update baseline top z t.2.rank
        rw [large,Function.update_self]
        exact minimum
    exact (tailDomination B m s t used).trans common
  obtain ⟨values,source,_⟩ := exactPaidCongruenceReads f B selected θ ls m s.constant s.terms
    setup.1 covers (fun t used => (setup.2.1 t used).2) paid
  let v := s.constant + actualSum s.terms values
  have real : valueAt f θ s.constant s.terms v := ⟨values,source,rfl⟩
  have tableCalibration := exactGreatestResidueTies f baseline top s.terms
  have sound (ν : Nat → Nat) (tied : PreparedTableTied f top baseline q.1 ν)
      (actual : Int) (live : valueAt f θ s.constant s.terms actual) :
      q.2.eval (Function.update ν 0 z) ↔ (Test.congruence m).atPolarity positive actual :=
    polarityIff m actual p (Function.update ν 0 z) positive
      (exactPaidCongruenceAtValue f B selected θ (Function.update ν 0 z) ls m s.constant s.terms actual
        setup.1 covers paid (tableCalibration.2 ν tied z) live)
  refine ⟨exactGreatestCongruenceShape top m s positive,?_⟩
  constructor
  · rintro ⟨ν,tied,passes⟩
    exact ⟨v,real,(sound ν tied v real).mp passes⟩
  · rintro ⟨actual,live,passes⟩
    obtain ⟨ν,tied⟩ := tableCalibration.1
    exact ⟨ν,tied,(sound ν tied actual live).mpr passes⟩

end LogicLineages.PermittedControl.ActualGreatestCongruenceRoute
