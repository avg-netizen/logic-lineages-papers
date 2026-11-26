import LogicLineages.PersistentMarking.CutStrictStrictSupport
namespace LogicLineages.PersistentMarking.CutStrictStrictProof
open Spine ExtendedMeasure CutSplitSupport

theorem strictStrict : CutOccurrenceTargets.StrictStrict := by
  intro S n below xs ys zs left right hcount ho
  obtain ⟨left⟩ := left
  cases left with
  | @multisetReplace xs lk lr ys lm la hls hlt hlnon hlmatch hlcover =>
    cases right with
    | @multisetReplace ys rk rr zs rm ra hrs hrt hrnon hrmatch hrcover =>
      obtain ⟨ac,ad,bc,bd,hmiddleA,hmiddleB,hmiddleC,hmiddleD⟩ := align hlt hrs
      obtain ⟨sourceC,sourceD,hsourceSplit,⟨hsourceC⟩,⟨hsourceD⟩⟩ := CutPartitionSupport.matchingTargetSplit hlmatch hmiddleA
      obtain ⟨targetC,targetE,htargetSplit,htargetC,htargetE,hcb,heb⟩ := CutSourcePartitionSupport.matchingSourceSplit hmiddleC hrmatch
      obtain ⟨removed,hnewsource,hremovedSplit⟩ := associate hls hsourceSplit
      obtain ⟨added,hnewtarget,haddedSplit⟩ := associate hrt htargetSplit
      have hnon : Spine.Nonempty removed := nonemptyRight hremovedSplit hlnon
      have hordinary := ConservativeListSupport.splitOrdinary hnewtarget ho
      have hmBound : treeSize hrmatch < n := by
        change 1 + treeSize hrmatch + treeSize hrcover < n at hcount
        omega
      have hcBound : treeSize hrcover < n := by
        change 1 + treeSize hrmatch + treeSize hrcover < n at hcount
        omega
      obtain ⟨hmatched⟩ := CutMatchingProof.weakWeak S n below sourceC ac targetC ⟨hsourceC⟩ htargetC (by omega) hordinary.1
      have hsuppliers : ∀ i q, At added i q → ∃ p j, At removed j p ∧ ExtendedStrict S p q := by
        intro i q hq
        have hordq := CutStrictWeakSupport.ordinaryAt hq hordinary.2
        rcases atSides haddedSplit hq with ⟨k,hk⟩ | ⟨k,hk⟩
        · obtain ⟨b,j,hb,edge,hbound⟩ := CutStrictWeakSupport.backAt htargetE hk
          obtain ⟨j',hb'⟩ := leftAt hmiddleB hb
          obtain ⟨p,jp,hp,hstrict⟩ := CutStrictWeakSupport.coverageAt hlcover hb'
          obtain ⟨jp',hp'⟩ := rightAt hremovedSplit hp
          exact ⟨p,jp',hp',CutEdgeProof.strictWeak S n below p b q hstrict edge (by omega) hordq⟩
        · obtain ⟨b,j,hb,edge,hbound⟩ := CutStrictStrictSupport.coverageAtBound hrcover hk
          rcases atSides hmiddleD hb with ⟨j',hb'⟩ | ⟨j',hb'⟩
          · obtain ⟨p,jp,hp,hweak⟩ := CutWeakStrictProof.matchingBackAt hsourceD hb'
            obtain ⟨jp',hp'⟩ := leftAt hremovedSplit hp
            exact ⟨p,jp',hp',CutEdgeProof.weakStrict S n below p b q hweak edge (by omega) hordq⟩
          · obtain ⟨j'',hb''⟩ := rightAt hmiddleB hb'
            obtain ⟨p,jp,hp,hstrict⟩ := CutStrictWeakSupport.coverageAt hlcover hb''
            obtain ⟨jp',hp'⟩ := rightAt hremovedSplit hp
            exact ⟨p,jp',hp',CutEdgeProof.strictStrict S n below p b q hstrict edge (by omega) hordq⟩
      obtain ⟨hcoverage⟩ := CutStrictWeakSupport.buildCoverage S removed added hsuppliers
      exact ⟨.multisetReplace hnewsource hnewtarget hnon hmatched hcoverage⟩
end LogicLineages.PersistentMarking.CutStrictStrictProof
