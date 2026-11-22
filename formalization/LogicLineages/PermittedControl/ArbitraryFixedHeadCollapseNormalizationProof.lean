module
public import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseTargets
import LogicLineages.OrdinalComparison.EncodedDescentProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.RawNotationCode
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryFixedHeadCollapse
open OrdinalComparison

theorem actualNormalization : ActualNormalization := by
  intro p normal
  let a : NONote := ⟨rawNoteDecode p.1,normal⟩
  have code : rawNoteEncode a.1 = p.1 := rawNoteEncodeDecode p.1
  have finite := encodedFiniteCorrect a
  rw [code] at finite
  refine ⟨finite.1,fun h => (finite.2 h).symm,?_⟩
  intro nonfinite
  let q := transported p
  have split := rawSplitActualCorrect a
  have normalLimit := rawSplitNormal a
  rw [code] at split normalLimit
  let lam : NONote := ⟨rawNoteDecode q.1,normalLimit⟩
  have part : lam.1.repr = actualLimitPart a.1.repr := split.1
  have lamCode : rawNoteEncode lam.1 = q.1 := rawNoteEncodeDecode q.1
  have norm := (rawNormCodeCorrect lam.1).trans (actualOrdinalNorm_notationCorrespondence lam).symm
  rw [lamCode] at norm
  have decomposition := actualNonfiniteDecomposition a.1.repr nonfinite (normalRepresentationSound a)
  have limit : Order.IsSuccLimit lam.1.repr := by
    rw [part]
    exact decomposition.2.1
  have arg : q.2 = actualOrdinalNorm lam.1.repr + (actualTailPart a.1.repr + p.2) := by
    change rawNormCode q.1 + ((rawSplitCode p.1).unpair.2 + p.2) = _
    rw [norm,split.2]
  have affordable : actualOrdinalNorm lam.1.repr ≤ q.2 := by
    rw [arg]
    exact Nat.le_add_right _ _
  have state : countInitial lam.1.repr q.2 = a.1.repr + (p.2 : Ordinal) := by
    rw [countInitial,arg,Nat.add_sub_cancel_left,Nat.cast_add,← add_assoc,part,
      ← decomposition.2.2.1]
  exact ⟨⟨lam.2,limit,affordable⟩,part,split.2,arg,state⟩

end LogicLineages.PermittedControl.ArbitraryFixedHeadCollapse
