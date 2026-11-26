module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeOwnProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparseRawRun (iterateState ownState)
open NumberedWindowInternalSparseRawTickShapeTargets (goodState)
open NumberedWindowInternalSparseRawRunShapeTargets
open NumberedWindowInternalSparseRawRunShapeInductionProof (loopShape)
open NumberedWindowInternalSparseRawRunShapeOwnProof (initialGraph ownShape)

theorem exact_OpenRawLoopShape : ExactOpenRawLoopShape := by
  intro body p other α fuel start out
  let s := goodState start
  let g := programGraph (iterateState p other) out ![fuel,start]
  obtain ⟨d⟩ := loopShape (body := body) (Γ := [g,s]) p other fuel start out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem exact_OpenInitialState : ExactOpenInitialState := by
  intro body α q w r
  exact initialGraph (body := body) (Γ := []) ![q,w,r]

theorem exact_OpenOwnStateShape : ExactOpenOwnStateShape := by
  intro body p other α q w r out
  let g := programGraph (ownState p other) out ![q,w,r]
  obtain ⟨d⟩ := ownShape (body := body) (Γ := [g]) p other out ![q,w,r]
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_OpenRawLoopShape
#print axioms exact_OpenInitialState
#print axioms exact_OpenOwnStateShape
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeChecks
