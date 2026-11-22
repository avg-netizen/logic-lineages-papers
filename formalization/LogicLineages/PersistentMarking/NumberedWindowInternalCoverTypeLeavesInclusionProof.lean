module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesInclusionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverTypeLeavesTargets
open NumberedWindowInternalCoverTypeLeavesOpenDataProof (reportRename)

attribute [local irreducible] programGraph

theorem exact_OpenCoverTypeLeavesInclusion : ExactOpenCoverTypeLeavesInclusion := by
  intro body α Γ out next K old new
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let hit := memberGraph (out.relabel j) key
  let Δ := hit :: Γ.map (fun q => q.relabel j)
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have old' := renameInto old j Δ keep
  have new' := renameInto new j Δ keep
  rw [reportRename] at old' new'
  have same := valueUnique typeLeaves (out.relabel j) (next.relabel j) (unaryTape (K.relabel j)) old' new'
  obtain ⟨moved⟩ := headTransport scratchMember (suc z) (out.relabel j) (next.relabel j) ![key] same
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction moved)⟩

#print axioms exact_OpenCoverTypeLeavesInclusion

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesInclusionProof
