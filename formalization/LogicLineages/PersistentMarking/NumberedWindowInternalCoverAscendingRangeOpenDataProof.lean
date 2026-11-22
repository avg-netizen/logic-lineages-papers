module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
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
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalCoverAscendingRangeTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem calls (bound out i : OTerm α)
    (h : Nonempty (Derivation body Γ (rangeReport out bound))) (k : Fin 2) :
    Nonempty (Derivation body Γ
      (programGraph ((![rangeOnFirst,.projection 1] : Fin 2 → Program 2) k)
        ((![out,i] : Fin 2 → OTerm α) k) ![bound,i])) := by
  have a : Nonempty (Derivation body Γ (programGraph rangeOnFirst out ![bound,i])) := by
    apply compositionValue ascendingRange (fun _ : Fin 1 => .projection 0)
      out ![bound,i] ![bound] h
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 0 ![bound,i]
  exact Fin.cases a (Fin.cases (projectionValue 1 ![bound,i]) (fun j => Fin.elim0 j)) k

theorem build (bound out i : OTerm α)
    (run : Nonempty (Derivation body Γ (rangeReport out bound)))
    (hit : Nonempty (Derivation body Γ (memberGraph out i))) :
    Nonempty (Derivation body Γ (rangeTest bound i)) :=
  compositionValue scratchMember ![rangeOnFirst,.projection 1]
    (suc z) ![bound,i] ![out,i] hit (calls bound out i run)

theorem recover (bound out i : OTerm α)
    (run : Nonempty (Derivation body Γ (rangeReport out bound)))
    (hit : Nonempty (Derivation body Γ (rangeTest bound i))) :
    Nonempty (Derivation body Γ (memberGraph out i)) :=
  compositionRecover scratchMember ![rangeOnFirst,.projection 1]
    (suc z) ![bound,i] ![out,i] hit (calls bound out i run)

private theorem endCase (bound previous out one i : OTerm α)
    (row : Nonempty (Derivation body Γ (programGraph rangeStep out ![bound,previous])))
    (single : Nonempty (Derivation body Γ (programGraph singleton one ![bound,previous])))
    (split : Nonempty (Derivation body Γ (ltF i bound ⊔ eqn i bound)))
    (ih : Nonempty (Derivation body Γ (atBound bound i)))
    (old : Nonempty (Derivation body Γ (rangeReport previous bound))) :
    Nonempty (Derivation body Γ (memberGraph out i)) := by
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
  let L := ltF i bound
  let E := eqn i bound
  obtain ⟨split⟩ := split
  obtain ⟨ih⟩ := ih
  obtain ⟨old⟩ := old
  obtain ⟨cell⟩ := cell
  obtain ⟨appended⟩ := appended
  have hleft : Nonempty (Derivation body (L :: Γ) (rangeTest bound i)) :=
    ⟨Derivation.implicationElimination (addHyp ih L) (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨earlier⟩ := fromLeft previous one out i ⟨addHyp appended L⟩
    (recover bound previous i ⟨addHyp old L⟩ hleft)
  obtain ⟨last⟩ := fromRight previous one out i ⟨addHyp appended E⟩
    (headMember one bound z i ⟨addHyp cell E⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction earlier)
    (Derivation.implicationIntroduction last)⟩

theorem afterStep (bound previous out i : OTerm α)
    (old : Nonempty (Derivation body Γ (rangeReport previous bound)))
    (run : Nonempty (Derivation body Γ (rangeReport out (suc bound))))
    (split : Nonempty (Derivation body Γ (ltF i bound ⊔ eqn i bound)))
    (ih : Nonempty (Derivation body Γ (atBound bound i))) :
    Nonempty (Derivation body Γ (memberGraph out i)) := by
  have row : Nonempty (Derivation body Γ (programGraph rangeStep out ![bound,previous])) :=
    recursionRecover (constantZero 0) rangeStep out previous bound Fin.elim0 old run
  apply programCases singleton ![bound,previous] _
  intro β j Δ one keep actual
  rw [graphRename]
  simp only [binaryInputsRename] at actual
  have movedRow := renameInto row j Δ keep
  have movedSplit := renameInto split j Δ keep
  have prior := renameInto old j Δ keep
  have movedIH := renameInto ih j Δ keep
  simp only [programRename,binaryInputsRename] at movedRow
  rw [ID1Completion.InternalBetaBoundaryProof.supRename,
    ID1Completion.InternalOriginalOrderSyntaxProof.orderRename,
    ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel] at movedSplit
  rw [unaryRename] at prior
  rw [NumberedWindowInternalCoverAscendingRangeSyntaxProof.atRename] at movedIH
  exact endCase (bound.relabel j) (previous.relabel j) (out.relabel j) one
    (i.relabel j) movedRow actual movedSplit movedIH

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenDataProof
