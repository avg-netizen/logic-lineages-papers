module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesFromIdsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap flatGraph)
open NumberedWindowInternalCoverCartesianFoldSyntaxProof (flatRename)
open NumberedWindowInternalCoverCartesianFoldThinOpenProof (exact_OpenCartesianFoldMember)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverNamedLeavesTargets
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename singletonMember)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem singletonAxis (tag : Nat) (ty i ids block : OTerm α)
    (hit : Nonempty (Derivation body Γ (memberGraph ids i)))
    (run : Nonempty (Derivation body Γ (programGraph (typeBlock tag) block ![ty,ids]))) :
    Nonempty (Derivation body Γ (memberGraph block (namedTerm tag ty i))) := by
  let D := singletonLeaf tag
  have inner : Nonempty (Derivation body Γ (flatGraph D block ids ![ty])) := by
    have h := recoverReordered (flatMap D) (![1,0] : Fin 2 → Fin 2) block ![ty,ids] run
    have tape : (fun j => (![ty,ids] : Fin 2 → OTerm α) ((![1,0] : Fin 2 → Fin 2) j)) =
        Fin.cons ids ![ty] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [tape] at h
    exact h
  apply programCases D ![i,ty] _
  intro β j Δ one keep singleton
  rw [graphRename,namedRename]
  simp only [binaryInputsRename] at singleton
  have h := renameInto hit j Δ keep
  have f := renameInto inner j Δ keep
  rw [graphRename] at h
  rw [flatRename,unaryInputsRename] at f
  exact exact_OpenCartesianFoldMember D body β Δ (ids.relabel j) (i.relabel j) one
    (namedTerm tag (ty.relabel j) (i.relabel j)) (block.relabel j) ![ty.relabel j]
    h singleton (singletonMember tag (ty.relabel j) (i.relabel j) one singleton) f

theorem exact_OpenCoverNamedFromIdsMember (tag : Nat) (K ty i ids out : OTerm α)
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hi : Nonempty (Derivation body Γ (memberGraph ids i)))
    (run : Nonempty (Derivation body Γ (flatGraph (typeBlock tag) out K ![ids]))) :
    Nonempty (Derivation body Γ (memberGraph out (namedTerm tag ty i))) := by
  let D := typeBlock tag
  apply programCases D ![ty,ids] _
  intro β j Δ block keep blockRun
  rw [graphRename,namedRename]
  simp only [binaryInputsRename] at blockRun
  have typeHit := renameInto ht j Δ keep
  have indexHit := renameInto hi j Δ keep
  have folded := renameInto run j Δ keep
  simp only [graphRename] at typeHit indexHit
  rw [flatRename,unaryInputsRename] at folded
  have one := singletonAxis tag (ty.relabel j) (i.relabel j) (ids.relabel j) block indexHit blockRun
  exact exact_OpenCartesianFoldMember D body β Δ (K.relabel j) (ty.relabel j) block
    (namedTerm tag (ty.relabel j) (i.relabel j)) (out.relabel j) ![ids.relabel j]
    typeHit blockRun one folded


#print axioms exact_OpenCoverNamedFromIdsMember

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesFromIdsProof
