module

public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenConsInverseProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue outputTransport valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalListCodec (consCode tailCode)
open ID1Completion.InternalListCodecSupportProof (consDestruction consGraphRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldCellSuccessProof (consToCell)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePairGraphProof (consEquation)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (scratchCursor scratchCurrent onCursor dead)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof
  (call6 stateParts atCursor moveSelected)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalParameterizedPositiveFold (stepAt updateAt advanceAt)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem liftAdvance (A : Program 4)
    (out k prior c ty start cert cur hop : OTerm α)
    (result : Nonempty (Derivation body Γ (programGraph A out ![c,ty,cur,hop])))
    (state : Nonempty (Derivation body Γ (programGraph scratchCurrent cur (call6 k prior c ty start cert))))
    (field : Nonempty (Derivation body Γ (programGraph (onCursor cellHead) hop (call6 k prior c ty start cert)))) :
    Nonempty (Derivation body Γ (programGraph (advanceAt A) out (call6 k prior c ty start cert))) := by
  let args := call6 k prior c ty start cert
  apply compositionValue A ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]
    out args ![c,ty,cur,hop] result
  intro i
  exact Fin.cases (projectionValue (2 : Fin 6) args) (Fin.cases (projectionValue (3 : Fin 6) args)
    (Fin.cases state (Fin.cases field (fun k => Fin.elim0 k)))) i

private theorem recoverActualAdvance (A : Program 4)
    (out k prior c ty start cert cur hop tail next : OTerm α)
    (updated : Nonempty (Derivation body Γ (programGraph (updateAt A) out (call6 k prior c ty start cert))))
    (state : Nonempty (Derivation body Γ (programGraph scratchCurrent cur (call6 k prior c ty start cert))))
    (head : Nonempty (Derivation body Γ (programGraph (onCursor cellHead) hop (call6 k prior c ty start cert))))
    (rest : Nonempty (Derivation body Γ (programGraph (onCursor cellTail) tail (call6 k prior c ty start cert))))
    (after : Nonempty (Derivation body Γ (scratchGraph out tail next))) :
    Nonempty (Derivation body Γ (programGraph A next ![c,ty,cur,hop])) := by
  apply programCases A (![c,ty,cur,hop] : Fin 4 → OTerm α) _
  intro β j Δ n keep actual
  rw [quadInputsRename] at actual
  let c' := c.relabel j
  let t' := ty.relabel j
  let k' := k.relabel j
  let out' := out.relabel j
  let prior' := prior.relabel j
  let start' := start.relabel j
  let cert' := cert.relabel j
  let cur' := cur.relabel j
  let hop' := hop.relabel j
  let tail' := tail.relabel j
  let next' := next.relabel j
  let args := call6 k' prior' c' t' start' cert'
  have work := moveSelected j Δ keep (updateAt A) out k prior c ty start cert updated
  have h := moveSelected j Δ keep (onCursor cellHead) hop k prior c ty start cert head
  have t := moveSelected j Δ keep (onCursor cellTail) tail k prior c ty start cert rest
  have s := moveSelected j Δ keep scratchCurrent cur k prior c ty start cert state
  have candidate := liftAdvance A n k' prior' c' t' start' cert' cur' hop' actual s h
  have found : Nonempty (Derivation body Δ (scratchGraph out' tail' n)) :=
    compositionRecover consCode ![onCursor cellTail,advanceAt A] out' args ![tail',n] work
      (fun i => Fin.cases t (Fin.cases candidate (fun a => Fin.elim0 a)) i)
  have wanted := renameInto after j Δ keep
  change Nonempty (Derivation body Δ ((ID1Completion.InternalListCodecSupportProof.consGraph out tail next).relabel j))
    at wanted
  rw [consGraphRename] at wanted
  obtain ⟨seen⟩ := consDestruction out' tail' n found
  obtain ⟨held⟩ := consDestruction out' tail' next' wanted
  have same := valueUnique tailCode n next' ![out']
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight seen)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight held)⟩
  rw [ID1Completion.InternalControlGraphSupportProof.programRename,quadInputsRename]
  exact outputTransport A n next' ![c',t',cur',hop'] same actual

/-- Inverse of the actual parameterized positive fold step at a visible
physical cons. Both scratch reports are original. The recovered A-call
has exactly the visible original head and carried before/after values. -/
theorem exact_OpenParameterizedConsTransitionInverse (A : Program 4)
    (out k prior c ty start cert cursor current hop tail next : OTerm α)
    (before : Nonempty (Derivation body Γ (scratchGraph prior cursor current)))
    (owner : Nonempty (Derivation body Γ (consGraph cursor hop tail)))
    (after : Nonempty (Derivation body Γ (scratchGraph out tail next)))
    (held : Nonempty (Derivation body Γ (programGraph (stepAt A) out (call6 k prior c ty start cert)))) :
    Nonempty (Derivation body Γ (programGraph A next ![c,ty,current,hop])) := by
  let args := call6 k prior c ty start cert
  obtain ⟨atRaw,atCurrent⟩ := stateParts cursor current k prior c ty start cert before
  obtain ⟨fields⟩ := consToCell cursor hop tail owner
  have good := atCursor cellGood (suc z) cursor args ⟨Derivation.conjunctionLeft fields⟩ atRaw
  have first := atCursor cellHead hop cursor args
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight fields)⟩ atRaw
  have rest := atCursor cellTail tail cursor args
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight fields)⟩ atRaw
  let pred := pairTerm hop tail
  have nonempty := outputTransport scratchCursor cursor (suc pred) args
    (consEquation cursor hop tail owner) atRaw
  have live := successorBranchElim scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateAt A)) out pred args nonempty held
  have update := successorBranchElim (onCursor cellGood) dead (updateAt A) out z args good live
  exact recoverActualAdvance A out k prior c ty start cert current hop tail next update atCurrent first rest after

#print axioms exact_OpenParameterizedConsTransitionInverse
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenConsInverseProof
