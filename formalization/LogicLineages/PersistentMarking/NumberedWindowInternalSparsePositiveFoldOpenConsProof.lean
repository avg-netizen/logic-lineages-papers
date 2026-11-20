module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenBaseProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSuccessProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue outputTransport)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldCellSuccessProof (consToCell)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePairGraphProof (consEquation)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem liftAdvance (raw : Program 5) (least : Program 3)
    (out k prior c ty start cert cur hop : OTerm α)
    (result : Nonempty (Derivation body Γ (selectedGraph raw least out c ty cur hop)))
    (state : Nonempty (Derivation body Γ (programGraph scratchCurrent cur (call6 k prior c ty start cert))))
    (field : Nonempty (Derivation body Γ (programGraph (onCursor cellHead) hop (call6 k prior c ty start cert)))) :
    Nonempty (Derivation body Γ (programGraph (advanceAtCell raw least) out (call6 k prior c ty start cert))) := by
  let args := call6 k prior c ty start cert
  apply compositionValue (advance raw least) ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]
    out args ![c,ty,cur,hop] result
  intro i
  exact Fin.cases (projectionValue (2 : Fin 6) args) (Fin.cases (projectionValue (3 : Fin 6) args)
    (Fin.cases state (Fin.cases field (fun k => Fin.elim0 k)))) i

private theorem consTransition (raw : Program 5) (least : Program 3)
    (out k prior c ty start cert cursor current hop tail next : OTerm α)
    (before : Nonempty (Derivation body Γ (scratchGraph prior cursor current)))
    (owner : Nonempty (Derivation body Γ (consGraph cursor hop tail)))
    (value : Nonempty (Derivation body Γ (selectedGraph raw least next c ty current hop)))
    (after : Nonempty (Derivation body Γ (scratchGraph out tail next))) :
    Nonempty (Derivation body Γ (stepGraph raw least out k prior c ty start cert)) := by
  let args := call6 k prior c ty start cert
  obtain ⟨atRaw,atCurrent⟩ := stateParts cursor current k prior c ty start cert before
  obtain ⟨fields⟩ := consToCell cursor hop tail owner
  have good := atCursor cellGood (suc z) cursor args ⟨Derivation.conjunctionLeft fields⟩ atRaw
  have first := atCursor cellHead hop cursor args
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight fields)⟩ atRaw
  have rest := atCursor cellTail tail cursor args
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight fields)⟩ atRaw
  have nextValue := liftAdvance raw least next k prior c ty start cert current hop value atCurrent first
  have updated : Nonempty (Derivation body Γ (programGraph (updateCell raw least) out args)) := by
    apply compositionValue consCode ![onCursor cellTail,advanceAtCell raw least]
      out args ![tail,next] after
    intro i
    exact Fin.cases rest (Fin.cases nextValue (fun k => Fin.elim0 k)) i
  have inner := successorBranchIntro (onCursor cellGood) dead (updateCell raw least) out z args good updated
  let pred := pairTerm hop tail
  have nonempty := outputTransport scratchCursor cursor (suc pred) args (consEquation cursor hop tail owner) atRaw
  exact successorBranchIntro scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateCell raw least)) out pred args nonempty inner

theorem consStep : OpenConsUpdate := by
  intro body raw least α out k prior c ty start cert cursor current hop tail next
  let a := scratchGraph prior cursor current ⊓
    (consGraph cursor hop tail ⊓ (selectedGraph raw least next c ty current hop ⊓ scratchGraph out tail next))
  have ha : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  have rhs := Derivation.conjunctionRight ha
  have r := Derivation.conjunctionRight rhs
  obtain ⟨out⟩ := consTransition raw least out k prior c ty start cert cursor current hop tail next
    ⟨Derivation.conjunctionLeft ha⟩ ⟨Derivation.conjunctionLeft rhs⟩
    ⟨Derivation.conjunctionLeft r⟩ ⟨Derivation.conjunctionRight r⟩
  exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenConsProof
