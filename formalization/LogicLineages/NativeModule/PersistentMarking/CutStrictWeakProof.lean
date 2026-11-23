module

public import LogicLineages.NativeModule.PersistentMarking.CutStrictWeakSupport
public import LogicLineages.NativeModule.PersistentMarking.CutMatchingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.CutStrictWeakProof
open Spine ExtendedMeasure

theorem strictWeak : CutOccurrenceTargets.StrictWeak := by
  intro S n below xs ys zs left right hc ho
  obtain ⟨left⟩ := left
  cases left with
  | multisetReplace hsource htarget hnon hmatching hcoverage =>
    obtain ⟨kept,added,hpartition,hkeep,hadded,hkb,hab⟩ := CutSourcePartitionSupport.matchingSourceSplit htarget right
    have hordinary := ConservativeListSupport.splitOrdinary hpartition ho
    obtain ⟨hcomp⟩ := CutMatchingProof.weakWeak S n below _ _ _ ⟨hmatching⟩ hkeep (by omega) hordinary.1
    obtain ⟨hcov⟩ := CutStrictWeakSupport.coverage S n below _ _ _ hcoverage hadded (by omega) hordinary.2
    exact ⟨.multisetReplace hsource hpartition hnon hcomp hcov⟩
end LogicLineages.PersistentMarking.CutStrictWeakProof
