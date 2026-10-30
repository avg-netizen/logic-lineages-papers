module
public import LogicLineages.OrdinalComparison.CollectedNonlinearBandTargets
public import LogicLineages.OrdinalComparison.CollectedWeightedPeakProof
public import LogicLineages.OrdinalComparison.CollectedAffineBandProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem collectedNonlinearInputBand : Targets.CollectedNonlinearInputBand := by
  intro rho c b tags hl he hv hn
  have hT : collectedNonlinearThreshold rho c b tags=
      max 4 (max (actualOrdinalNorm rho.1.repr+c+b) (2*collectedCoefficientSum tags+1)) := by
    rw [actualOrdinalNorm_notationCorrespondence rho]
    rfl
  refine ⟨hT,?_⟩
  intro x hx
  rw [hT] at hx
  have hx4 : 4≤x := (le_max_left _ _).trans hx
  have hfields := (le_max_right _ _).trans hx
  have hab : actualOrdinalNorm rho.1.repr+c+b≤x := (le_max_left _ _).trans hfields
  have hk : 2*collectedCoefficientSum tags+1≤x := (le_max_right _ _).trans hfields
  let t := actualOrdinalNorm (actualCollectedTagInput rho (.mk c b tags) x)
  let Y := actualCollectedMaximumPeak tags x
  let C := collectedCoefficientSum tags
  change Phi x<t ∧ ControlRoot t ∧ ∃ s : Nat, Y=Phi s ∧ Y<t ∧ t<(2*C+1)*Y ∧ (2*C+1)*Y<Phi (s+1)
  have hnorm : t=actualOrdinalNorm rho.1.repr+c+b*x+actualCollectedTagsEval tags x :=
    collectedAtomNormDecomposition rho c b tags hl he x
  have hw := collectedWeightedPeakBand tags hv hn x (by omega)
  change Y<actualCollectedTagsEval tags x ∧ actualCollectedTagsEval tags x<2*C*Y ∧ ∃ s, Y=Phi s at hw
  obtain ⟨hYsum,hsum,s,hs⟩ := hw
  have hY : Phi x≤Y := (collectedMaximumPeak tags hv hn x (by omega)).2.1
  have hxs : x≤s := by
    by_contra h
    have hlt := Phi_strictMono (show s<x by omega)
    rw [←hs] at hlt
    omega
  have hgap : (2*C+1)*Y<Phi (s+1) := by
    rw [hs]
    exact phiMultiplicativeStepGap s _ (hk.trans hxs)
  have haff : actualOrdinalNorm rho.1.repr+c+b*x≤Y := by
    have ha := Nat.mul_le_mul_left (actualOrdinalNorm rho.1.repr+c) (show 1≤x by omega)
    simp only [Nat.mul_one] at ha
    calc
      actualOrdinalNorm rho.1.repr+c+b*x≤(actualOrdinalNorm rho.1.repr+c)*x+b*x := Nat.add_le_add_right ha _
      _=(actualOrdinalNorm rho.1.repr+c+b)*x := (Nat.add_mul _ _ _).symm
      _≤x*x := Nat.mul_le_mul_right x hab
      _≤Phi x := (actualPhiSquareGap x).le
      _≤Y := hY
  have hYt : Y<t := by rw [hnorm]; omega
  have ht : t<(2*C+1)*Y := by
    rw [hnorm]
    calc
      actualOrdinalNorm rho.1.repr+c+b*x+actualCollectedTagsEval tags x≤Y+actualCollectedTagsEval tags x :=
        Nat.add_le_add_right haff _
      _<Y+2*C*Y := Nat.add_lt_add_left hsum _
      _=(2*C+1)*Y := by rw [Nat.add_mul,Nat.one_mul]; omega
  have hroot : ControlRoot t := phiBetweenImagesRoot s t (by rw [←hs]; exact hYt) (ht.trans hgap)
  exact ⟨hY.trans_lt hYt,hroot,s,hs,hYt,ht,hgap⟩

end LogicLineages.OrdinalComparison
