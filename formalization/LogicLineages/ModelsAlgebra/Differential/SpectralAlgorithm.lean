module

public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmInputs
public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode
public import LogicLineages.ModelsAlgebra.Differential.SpectralResultant
public import LogicLineages.ModelsAlgebra.Differential.SpectralConstraint
public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm

universe u

private theorem box_mono {n B C : ℕ} (hBC : B ≤ C) {p : MvPolynomial (Fin n) ℚ}
    (hp : KroneckerPolynomial.Box B p) : KroneckerPolynomial.Box C p := by
  intro d hd i
  exact (hp d hd i).trans_le hBC

private theorem rebase_value (n B C : ℕ) (hB : 2 ≤ B) (hC : 2 ≤ C) (hBC : B ≤ C)
    (a : DensePolynomial.Code) :
    BoxPolynomialCode.value n C (BoxPolynomialCode.rebase n B C a) =
      BoxPolynomialCode.value n B a := by
  rw [BoxPolynomialCode.value, BoxPolynomialCode.rebase_calibration n B C a]
  exact KroneckerPolynomial.decode_encode ℚ n C hC (BoxPolynomialCode.value n B a)
    (box_mono hBC (BoxPolynomialCode.bound n B hB a))

theorem search_correct : Targets.spectralAlgorithmSearchCorrect.{u} := by
  intro t answer hp ha
  obtain ⟨hB, hq, hm, hpos, root, hli, hfac⟩ := hp
  let f := equation t
  let n := f.natDegree
  let q : MvPolynomial (Fin n) ℚ := lowerPolynomial t
  let C := sourceBase n
  let B := max C t.2.1
  let R := SpectralResultant.obstruction n f
  let rc := SpectralResultantCode.obstruction n C t.1
  have hn : order t = n := order_correct t
  have hC : 2 ≤ C := by dsimp [C, sourceBase]; omega
  have hcommon : 2 ≤ B := hC.trans (le_max_left _ _)
  have hRbox : KroneckerPolynomial.Box (n + 1) R :=
    SpectralResultant.resultant_box f.SplittingField n f root hpos hm rfl hfac
  have hRvalue : BoxPolynomialCode.value n C rc = R := by
    rw [BoxPolynomialCode.value, SpectralResultantCode.obstruction_correct n C t.1]
    change KroneckerPolynomial.decode C n (KroneckerPolynomial.encode C R) = R
    apply KroneckerPolynomial.decode_encode ℚ n C hC R
    exact box_mono (by dsimp [C, sourceBase]; omega) hRbox
  have hleft : BoxPolynomialCode.value n B (BoxPolynomialCode.rebase n C B rc) = R := by
    rw [rebase_value n C B hC hcommon (le_max_left _ _), hRvalue]
  have hright : BoxPolynomialCode.value n B
      (BoxPolynomialCode.rebase n t.2.1 B t.2.2) = q :=
    rebase_value n t.2.1 B hB hcommon (le_max_right _ _) t.2.2
  have ha' : answer ∈ BoundedPolynomialDivision.search
      (n, B, BoxPolynomialCode.rebase n C B rc,
        BoxPolynomialCode.rebase n t.2.1 B t.2.2) := by
    simpa only [search, prepare, hn] using ha
  have hdiv := BoundedPolynomialDivision.search_correct n B hcommon
    (BoxPolynomialCode.rebase n C B rc) (BoxPolynomialCode.rebase n t.2.1 B t.2.2) answer ha'
  rw [hleft, hright] at hdiv
  have hRmap := SpectralResultant.resultant_calibration f.SplittingField n f root hm rfl hfac
  have hcrit := SpectralConstraint.criterion.{u} f root hm hpos hli hfac R hRmap q hq
  exact hdiv.trans hcrit.symm

end LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm
