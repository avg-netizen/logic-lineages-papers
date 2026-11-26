module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue successorValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap flatGraph)
open NumberedWindowInternalCoverCartesianFoldSyntaxProof (flatRename)
open NumberedWindowInternalCoverCartesianFoldThinOpenProof (exact_OpenCartesianFoldMember)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange rangeReport)
open NumberedWindowInternalCoverAscendingRangeOpenProof (exact_OpenCoverAscendingRangeMember)
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

private theorem bothAxes (tag : Nat) (K ty i ids out : OTerm α)
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

private theorem actualIds (K M ids : OTerm α)
    (run : Nonempty (Derivation body Γ (rangeReport ids (suc M)))) :
    Nonempty (Derivation body Γ (programGraph idsAt ids ![K,M])) := by
  let xs : Fin 2 → OTerm α := ![K,M]
  have next : Nonempty (Derivation body Γ (programGraph boundSuccessor (suc M) xs)) := by
    apply compositionValue (.succ : Program 1) (fun _ : Fin 1 => .projection 1)
      (suc M) xs ![M] (successorValue ![M])
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  apply compositionValue ascendingRange (fun _ : Fin 1 => boundSuccessor) ids xs ![suc M] run
  intro i
  obtain rfl := Fin.eq_zero i
  exact next

private theorem fromRange (isBound : Bool) (out K ty i M ids : OTerm α)
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (large : Nonempty (Derivation body Γ (ltF i (suc M))))
    (named : Nonempty (Derivation body Γ (namedReport isBound out K M)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M)))) :
    Nonempty (Derivation body Γ (memberGraph out (namedTerm isBound.toNat ty i))) := by
  let xs : Fin 2 → OTerm α := ![K,M]
  have cutoff := actualIds K M ids range
  have hi := exact_OpenCoverAscendingRangeMember body α Γ ids (suc M) i range large
  have folded : Nonempty (Derivation body Γ (flatGraph (typeBlock isBound.toNat) out K ![ids])) := by
    apply compositionRecover (namedFromIds isBound.toNat)
      (Fin.cons (.projection 0) (Fin.cons idsAt Fin.elim0)) out xs ![K,ids] named
    intro j
    exact Fin.cases (projectionValue 0 xs) (Fin.cases cutoff (fun k => Fin.elim0 k)) j
  exact bothAxes isBound.toNat K ty i ids out ht hi folded

theorem exact_OpenCoverNamedLeafAtLargerBound : ExactOpenCoverNamedLeafAtLargerBound := by
  intro isBound body α Γ out K ty i m M ht hsmall hgrow named
  have bounds := weakTrans i m M hsmall hgrow
  apply programCases ascendingRange ![suc M] _
  intro β j Δ ids keep actual
  rw [graphRename,namedRename]
  simp only [unaryInputsRename,sucRelabel] at actual
  have member := renameInto ht j Δ keep
  have h := renameInto bounds j Δ keep
  have leaf := renameInto named j Δ keep
  rw [graphRename] at member
  rw [orderRename,sucRelabel] at h
  simp only [namedReport,programRename,binaryInputsRename] at leaf
  exact fromRange isBound (out.relabel j) (K.relabel j) (ty.relabel j) (i.relabel j)
    (M.relabel j) ids member h leaf actual

#print axioms exact_OpenCoverNamedLeafAtLargerBound

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenProof
