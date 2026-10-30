module
public import LogicLineages.OrdinalComparison.PeakWordTargets
public import LogicLineages.OrdinalComparison.PrincipalBlocksProof
public import LogicLineages.OrdinalComparison.PrincipalWordActionProof
public import LogicLineages.OrdinalComparison.ActualTerminal

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem fullActualPrincipalPeakWord : Targets.FullActualPrincipalPeakWord := by
  intro o hl n
  let es := principalExponentBlocks o.1
  let word := principalKernelWord es 0
  let initial := o.1.repr + (n : Ordinal)
  let t := Vendor.R1.treeWeight o.1 + n
  have hd := actualPrincipalBlocksDenotation o.1 o.2
  have hno := actualPrincipalBlocksNormalOrder o.1 o.2
  have hld := actualPrincipalBlocksLimitDomain o.1 o.2 hl
  have hg : GenuinePrincipalBlocks es :=
    ⟨fun e he => ⟨hno.1 e he, hld.2 e he⟩, hno.2⟩
  have hw : principalBlocksWeight es = Vendor.R1.treeWeight o.1 :=
    hd.2.trans (actualOrdinalNorm_notationCorrespondence o)
  have hsum : principalBlockSum es = o.1.repr := hd.1
  have hword : word ≠ [] := by
    intro hz
    have hlen := congrArg List.length (actualPrincipalKernelWordPositions es 0)
    change word.length = _ at hlen
    rw [hz] at hlen
    have hes : es = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    exact hld.1 hes
  have hi := actualFiniteTailClosureNorm o.1.repr (normalRepresentationSound o) n
  have hnorm : actualOrdinalNorm initial = t := by
    rw [hi.2, actualOrdinalNorm_notationCorrespondence o]
  have hzero : compensatedPrefixControl 0 = Phi := by
    funext k
    simp [compensatedPrefixControl]
  have hr := actualPrincipalWordRunCorrect es hg 0 n
  dsimp only at hr
  rw [Nat.zero_add, hw, hsum, hzero, actualControlledCountPhiAgreement initial hi.1] at hr
  have hv := actualTerminalValueIdentities initial hi.1
  rw [hnorm] at hv
  have hrun : actualPrincipalWordRun word t =
      (actualTerminalValue initial, actualReplacementCount initial) := by
    rw [hv.2]
    exact hr
  have hgen := actualPrincipalWordInputsGenuine es hg 0 n
  rw [Nat.zero_add, hw] at hgen
  have hpos := (actualCompleteTerminalDecomposition o.1.repr (normalRepresentationSound o) hl
    (actualOrdinalNorm o.1.repr + n) (Nat.le_add_right _ _)).2.2.1
  simp only [Nat.add_sub_cancel_left] at hpos
  refine ⟨hword, hrun, hgen, ?_, ?_⟩
  · rw [hrun]
    exact hpos
  · rw [hrun]
    exact hv.1

end LogicLineages.OrdinalComparison
