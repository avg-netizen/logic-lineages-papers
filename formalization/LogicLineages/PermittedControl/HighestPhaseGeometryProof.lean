module
public import LogicLineages.PermittedControl.ProfileBoundaryProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem highestPhaseGeometry : Targets.HighestPhaseGeometry := by
  intro mu nu E n hselected
  have hmu := normalRepresentationSound mu
  have hnu := normalRepresentationSound nu
  have hE := normalRepresentationSound E
  rcases highestPieceSome mu nu E n hselected with ⟨hnf,hz,hzN,hz2,hzE,hzne,hmax,hhighest,hsign⟩
  let z := (rawNoteDecode n).repr
  let M := 3+actualOrdinalNorm mu.1.repr+actualOrdinalNorm nu.1.repr+actualOrdinalNorm E.1.repr
  have hzpos : 0 < z := (by norm_num : (0 : Ordinal) < 2).trans_le hz2
  obtain ⟨a,U,haz,hzU,hUE,haMem,hUMem,hband⟩ := profile_piece_boundaries mu.1.repr nu.1.repr E.1.repr z hzpos hzE
  have hneq (y : Ordinal.{0}) (hs : SameProfilePiece mu.1.repr nu.1.repr y z) :
      relativeProfile mu.1.repr y ≠ relativeProfile nu.1.repr y := by
    have hc := jointProfilePieceConstant mu.1.repr nu.1.repr y z hmu hnu hs
    intro heq
    exact hzne (hc.1.symm.trans (heq.trans hc.2))
  by_cases hUlt : U < E.1.repr
  · have hUm : U ∈ jointProfileBreakpoints mu.1.repr nu.1.repr := by
      rcases hUMem with hEq | hMem
      · exact False.elim (hUlt.ne hEq)
      · exact hMem
    have hUb := joint_breakpoint_norm_bound mu.1.repr nu.1.repr U hmu hnu hUm
    have hUn := (actualFiniteTailClosureNorm U hUb.1 1).2
    have hUM : actualOrdinalNorm (U+1) ≤ M := by
      simp only [Nat.cast_one] at hUn
      dsimp only [M]
      omega
    have hsame := hband U (haz.trans_le hzU) le_rfl
    left
    refine ⟨U,hz2.trans hzU,hUlt,hUlt.trans hE,hUM,hsame,hneq U hsame,?_,hsign U hsame⟩
    intro e hUe heE
    by_contra hne
    have hsame' := hhighest e (hz2.trans (hzU.trans hUe.le)) heE hne (hzU.trans_lt hUe)
    have heU := (hsame' U hUm).mpr hzU
    exact (not_le_of_gt hUe) heU
  · have hUEq : U=E.1.repr := le_antisymm hUE (le_of_not_gt hUlt)
    rcases Ordinal.zero_or_succ_or_isSuccLimit E.1.repr with hzero | ⟨beta,hbeta⟩ | hlim
    · exact False.elim ((not_lt_of_ge (show (0 : Ordinal) ≤ z from bot_le)) (by simpa only [hzero] using hzE))
    · have hbetaEq : E.1.repr=beta+1 := by simpa only [Order.succ_eq_add_one] using hbeta.symm
      have hzb : z ≤ beta := Order.lt_add_one_iff.mp (by rwa [← hbetaEq])
      have hbE : beta < E.1.repr := by rw [hbetaEq]; exact Order.lt_add_one_iff.mpr le_rfl
      have hbU : beta ≤ U := by rw [hUEq]; exact hbE.le
      have hsame := hband beta (haz.trans_le hzb) hbU
      have hbM : actualOrdinalNorm (beta+1) ≤ M := by rw [← hbetaEq]; dsimp only [M]; omega
      left
      refine ⟨beta,hz2.trans hzb,hbE,hbE.trans hE,hbM,hsame,hneq beta hsame,?_,hsign beta hsame⟩
      intro e hbe heE
      have heb : e ≤ beta := Order.lt_add_one_iff.mp (by rwa [← hbetaEq])
      exact False.elim ((not_le_of_gt hbe) heb)
    · let zeta : Ordinal.{0} := max 2 (a+1)
      have hza : a < zeta := (show a < a+1 from Order.lt_add_one_iff.mpr le_rfl).trans_le (le_max_right _ _)
      have hzetaz : zeta ≤ z := max_le hz2 (Order.add_one_le_iff.mpr haz)
      have hzetaE : zeta < E.1.repr := hzetaz.trans_lt hzE
      have hzetab : zeta < epsilonZero := hzetaE.trans hE
      have hab : a < epsilonZero := haz.trans hz
      have haN : actualOrdinalNorm a ≤ actualOrdinalNorm mu.1.repr+actualOrdinalNorm nu.1.repr := by
        rcases haMem with ha0 | ham
        · rw [ha0]
          have h0 : actualOrdinalNorm 0=0 := by simpa using actualFiniteHeadNorm 0 0
          rw [h0]
          omega
        · exact (joint_breakpoint_norm_bound mu.1.repr nu.1.repr a hmu hnu ham).2
      have hzetaM : actualOrdinalNorm zeta ≤ M := by
        by_cases htwo : (2 : Ordinal) ≤ a+1
        · have heq : zeta=a+1 := max_eq_right htwo
          rw [heq]
          have hsucc := (actualFiniteTailClosureNorm a hab 1).2
          simp only [Nat.cast_one] at hsucc
          dsimp only [M]
          omega
        · have heq : zeta=2 := max_eq_left (le_of_not_ge htwo)
          rw [heq]
          have h2 : actualOrdinalNorm (2 : Ordinal)=2 := by simpa using actualFiniteHeadNorm 0 2
          rw [h2]
          dsimp only [M]
          omega
      have hwhole : ∀ e : Ordinal.{0}, zeta ≤ e → e < E.1.repr → SameProfilePiece mu.1.repr nu.1.repr e z := by
        intro e hze heE
        exact hband e (hza.trans_le hze) (by rw [hUEq]; exact heE.le)
      have hsame := hwhole zeta le_rfl hzetaE
      right
      refine ⟨hlim,zeta,le_max_left _ _,hzetaE,hzetab,hzetaM,hwhole,hneq zeta hsame,?_,hsign zeta hsame⟩
      intro e hze heE
      have he := jointProfilePieceConstant mu.1.repr nu.1.repr e z hmu hnu (hwhole e hze heE)
      have hzeta := jointProfilePieceConstant mu.1.repr nu.1.repr zeta z hmu hnu hsame
      exact ⟨he.1.trans hzeta.1.symm,he.2.trans hzeta.2.symm⟩

end LogicLineages.PermittedControl
