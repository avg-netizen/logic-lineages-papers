import LogicLineages.PersistentMarking.NumberedWindowFixedExchangeSymmetryTargets

namespace LogicLineages.PersistentMarking.NumberedWindowFixedExchangeSymmetryChecks

open NumberedWindowArithmeticExchangeAtomsTargets (pairs)
open NumberedWindowExchangeAtoms (allowed)
open NumberedWindowHeadEnumerationTargets (equivalentHeads)
open NumberedWindowFixedExchangeSymmetryTargets

theorem exact_FixedHeadPairsSymmetry : ExactFixedHeadPairsSymmetry := by
  intro S K a b
  apply Bool.eq_iff_iff.mpr
  simp only [allowed,pairs,List.mem_flatMap,List.mem_map,decide_eq_true_eq,
    equivalentHeads,List.mem_filter,Prod.mk.injEq]
  constructor
  · rintro ⟨f,hf,g,⟨hg,sameRank⟩,first,second⟩
    exact ⟨g,hg,f,⟨hf,sameRank.symm⟩,second,first⟩
  · rintro ⟨g,hg,f,⟨hf,sameRank⟩,second,first⟩
    exact ⟨f,hf,g,⟨hg,sameRank.symm⟩,first,second⟩

#print axioms exact_FixedHeadPairsSymmetry

end LogicLineages.PersistentMarking.NumberedWindowFixedExchangeSymmetryChecks
