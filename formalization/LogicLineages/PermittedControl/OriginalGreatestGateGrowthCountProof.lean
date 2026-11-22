module
public import LogicLineages.PermittedControl.OriginalGreatestGateGrowthTargets
import LogicLineages.PermittedControl.ActualCountLeadingErrorProof
import LogicLineages.PermittedControl.SelectedLeadingSignCutoffActualProof
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsGrowthProof
import LogicLineages.PermittedControl.ActualShortCountCleanupCountProof
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.EntryLinearProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalGreatestGateGrowth
open OrdinalComparison FieldComparison PreparedProjection
open Targets (countCoreConstant)
open OriginalNaturalFieldGates (Gate)

theorem exactLongCountBound : ExactLongCountBound := by
  intro lam mu
  simp only [longCountBound,longCountBoundCode,normal_norm_code,countCoreConstant]

theorem exactLongCountStrictGrowth : ExactLongCountStrictGrowth := by
  intro f B hf ρ rank lam mu v y long paid yLe actual
  let x := ρ rank
  let κ := countCoreConstant mu.1.repr
  rw [exactLongCountBound lam mu] at paid
  have norms : max (actualOrdinalNorm lam.1.repr) (actualOrdinalNorm mu.1.repr+3) ≤ x :=
    max_le ((le_max_left _ _).trans paid)
      ((le_max_left _ _).trans ((le_max_right _ _).trans paid))
  have sign : SelectedLeadingSignCutoff.cutoff 2 κ.natAbs ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans paid)
  obtain ⟨_,i,_,data⟩ :=
    ActualCountLeadingError.exactActualCountLeadingError f B hf ρ rank lam mu v long norms actual
  let q := entryNormAt f (countInitial lam.1.repr x) i
  let C := f q
  have lead : f x ≤ C := data.2.2.1
  have base : 2 * (v : Int) = (C : Int) + 2 * ((i : Int)+κ) := data.2.2.2.2.1
  have abs : ((i : Int)+κ).natAbs ≤ Nat.log2 C + κ.natAbs := data.2.2.2.2.2.1
  have yLog : y ≤ Nat.log2 C :=
    yLe.trans (SelectedNonlinearImageBounds.rawCoordinateLogBound f B hf x C lead)
  let error := (i : Int)+κ-(y : Int)
  let total := (v : Int)-(y : Int)
  have triangle : error.natAbs ≤ ((i : Int)+κ).natAbs + y := by
    change (((i : Int)+κ) + -(y : Int)).natAbs ≤ _
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using Int.natAbs_add_le ((i : Int)+κ) (-(y : Int))
  have budget : error.natAbs ≤ 2 * Nat.log2 C + κ.natAbs := by omega
  have split : 2 * total = 1 * (C : Int) + 2 * error := by
    dsimp only [total,error]
    omega
  have conclusion := SelectedLeadingSignCutoff.actualLeadingSign f B hf x C 2 κ.natAbs 1 total error
    sign lead (by decide) split budget
  exact conclusion.1.mpr (by decide)

theorem exactShortCountGraph : ExactShortCountGraph := by
  intro f B hf θ lam mu source out hshort
  let k := shortGapLength lam mu
  change (ClosedOrdinaryValueDomain (.entry 0 lam mu) (θ source) ∧
      FirstEntry f (countInitial lam.1.repr (θ source)) mu.1.repr (θ out)) ↔ _
  constructor
  · rintro ⟨dom,seen⟩
    have real : LowerOperandActual f θ (.count source lam mu) (θ out) := ⟨dom,seen⟩
    exact ⟨dom.1,dom.2,ActualShortCountCleanup.exactPositiveShortCount f B hf θ source lam mu (θ out)
      hshort real⟩
  · rintro ⟨proper,affordable,outValue⟩
    have hλ : lam.1.repr = mu.1.repr + Ordinal.omega0 * (k : Ordinal) :=
      (shortGapRecognition lam mu proper k hshort).2.2.mp rfl
    have under := proper.2.2.trans (normalRepresentationSound lam)
    have entered := linear_entry f (selected_threshold_admissible f B hf).2
      mu.1.repr proper.2.1 under k (θ source-actualOrdinalNorm lam.1.repr)
    have start : countInitial lam.1.repr (θ source) =
        mu.1.repr + (Ordinal.omega0 * (k : Ordinal) +
          ((θ source-actualOrdinalNorm lam.1.repr : Nat) : Ordinal)) := by
      change lam.1.repr + ((θ source-actualOrdinalNorm lam.1.repr : Nat) : Ordinal) = _
      rw [hλ,add_assoc]
    rw [← start] at entered
    exact ⟨⟨proper,affordable⟩,outValue.symm ▸ entered⟩

end LogicLineages.PermittedControl.OriginalGreatestGateGrowth
