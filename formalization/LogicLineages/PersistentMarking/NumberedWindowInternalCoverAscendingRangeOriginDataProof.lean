module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalLeastNumberProof (actualRightSuccessorSplit)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalRawListRecursionSupportProof (recursionRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalScratchAppendOriginChecks (exact_OpenScratchAppendOrigin)
open NumberedWindowInternalCoverAscendingRangeOriginTargets
open NumberedWindowInternalCoverAscendingRangeOriginSyntaxProof (backRename)
open NumberedWindowInternalCoverAscendingRangeOpenDataProof (build)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open ID1Completion.InternalSquareRootArithmeticSupportProof (rightSuccessor orderRight)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans addZero addSucc congSuc sucNeZeroApply)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalCoverAscendingRangeTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem nilHit (i : OTerm α)
    (hit : Nonempty (Derivation body Γ (memberGraph z i))) :
    Nonempty (Derivation body Γ (⊥ : Formula α)) := by
  have impossible := nilRecover memberBase memberStep (suc z) ![i] hit
  obtain ⟨eq⟩ := valueUnique memberBase (suc z) z ![i] impossible (zeroConstantValue _)
  exact ⟨sucNeZeroApply eq⟩

private theorem selfWeak (n : OTerm α) :
    Nonempty (Derivation body Γ (ltF n (suc n))) := by
  apply actualOriginalOrderIntroduction body α Γ n (suc n) z
  rw [onEquality]
  exact ⟨trans (addSucc n z) (congSuc (addZero n))⟩

private theorem lastCase (one bound i : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph one bound z)))
    (hit : Nonempty (Derivation body Γ (memberGraph one i))) :
    Nonempty (Derivation body Γ (ltF i (suc bound))) := by
  obtain ⟨split⟩ := consInversion one bound z i cell hit
  let H := (missGraph bound i).not
  let T := memberGraph z i
  obtain ⟨eq⟩ := nonzeroEquality (body := body) (Γ := H :: Γ) bound i
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨self⟩ := selfWeak (body := body) (Γ := H :: Γ) i
  have last := orderRight i (congSuc (symm eq)) self
  obtain ⟨bottom⟩ := nilHit (body := body) (Γ := T :: Γ) i
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction last)
    (Derivation.implicationIntroduction (Derivation.explosion bottom))⟩

private theorem endCase (bound previous out one i : OTerm α)
    (row : Nonempty (Derivation body Γ (programGraph rangeStep out ![bound,previous])))
    (single : Nonempty (Derivation body Γ (programGraph singleton one ![bound,previous])))
    (member : Nonempty (Derivation body Γ (memberGraph out i)))
    (ih : Nonempty (Derivation body Γ (backBound bound i)))
    (old : Nonempty (Derivation body Γ (rangeReport previous bound))) :
    Nonempty (Derivation body Γ (ltF i (suc bound))) := by
  let xs : Fin 2 → OTerm α := ![bound,previous]
  have appended : Nonempty (Derivation body Γ (programGraph append out ![previous,one])) := by
    apply compositionRecover append (![.projection 1,singleton] : Fin 2 → Program 2)
      out xs ![previous,one] row
    intro j
    exact Fin.cases (projectionValue 1 xs) (Fin.cases single (fun k => Fin.elim0 k)) j
  have cell : Nonempty (Derivation body Γ (consGraph one bound z)) := by
    apply compositionRecover consCode (![.projection 0,constantZero 2] : Fin 2 → Program 2)
      one xs ![bound,z] single
    intro j
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (zeroConstantValue xs) (fun k => Fin.elim0 k)) j
  obtain ⟨split⟩ := exact_OpenScratchAppendOrigin body α Γ previous one out i appended member
  let L := memberGraph previous i
  let R := memberGraph one i
  obtain ⟨ih⟩ := ih
  obtain ⟨old⟩ := old
  obtain ⟨cell⟩ := cell
  obtain ⟨tested⟩ := build (body := body) (Γ := L :: Γ) bound previous i ⟨addHyp old L⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨earlier⟩ := rightSuccessor (body := body) (Gamma := L :: Γ) i bound
    ⟨Derivation.implicationElimination (addHyp ih L) tested⟩
  obtain ⟨last⟩ := lastCase (body := body) (Γ := R :: Γ) one bound i
    ⟨addHyp cell R⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction earlier)
    (Derivation.implicationIntroduction last)⟩

theorem afterStep (bound previous out i : OTerm α)
    (old : Nonempty (Derivation body Γ (rangeReport previous bound)))
    (run : Nonempty (Derivation body Γ (rangeReport out (suc bound))))
    (member : Nonempty (Derivation body Γ (memberGraph out i)))
    (ih : Nonempty (Derivation body Γ (backBound bound i))) :
    Nonempty (Derivation body Γ (ltF i (suc bound))) := by
  have row : Nonempty (Derivation body Γ (programGraph rangeStep out ![bound,previous])) :=
    recursionRecover (constantZero 0) rangeStep out previous bound Fin.elim0 old run
  apply programCases singleton ![bound,previous] _
  intro β j Δ one keep actual
  rw [ID1Completion.InternalOriginalOrderSyntaxProof.orderRename,
    ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel]
  simp only [binaryInputsRename] at actual
  have movedRow := renameInto row j Δ keep
  have movedMember := renameInto member j Δ keep
  have prior := renameInto old j Δ keep
  have movedIH := renameInto ih j Δ keep
  simp only [programRename,binaryInputsRename] at movedRow
  rw [graphRename] at movedMember
  change Nonempty (Derivation body Δ ((NumberedWindowInternalSparsePathEnvelopeTargets.unary
    ascendingRange previous bound).relabel j)) at prior
  rw [unaryRename] at prior
  rw [backRename] at movedIH
  exact endCase (bound.relabel j) (previous.relabel j) (out.relabel j) one
    (i.relabel j) movedRow actual movedMember movedIH prior

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginDataProof
