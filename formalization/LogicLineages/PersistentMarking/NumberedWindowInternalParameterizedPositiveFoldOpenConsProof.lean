module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenBaseProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSuccessProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenConsProof
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
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof
open NumberedWindowInternalParameterizedPositiveFold

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

theorem exact_OpenParameterizedConsTransition (A : Program 4)
    (out k prior c ty start cert cursor current hop tail next : OTerm α)
    (before : Nonempty (Derivation body Γ (scratchGraph prior cursor current)))
    (owner : Nonempty (Derivation body Γ (consGraph cursor hop tail)))
    (value : Nonempty (Derivation body Γ (programGraph A next ![c,ty,current,hop])))
    (after : Nonempty (Derivation body Γ (scratchGraph out tail next))) :
    Nonempty (Derivation body Γ (programGraph (stepAt A) out (call6 k prior c ty start cert))) := by
  let args := call6 k prior c ty start cert
  obtain ⟨atRaw,atCurrent⟩ := stateParts cursor current k prior c ty start cert before
  obtain ⟨fields⟩ := consToCell cursor hop tail owner
  have good := atCursor cellGood (suc z) cursor args ⟨Derivation.conjunctionLeft fields⟩ atRaw
  have first := atCursor cellHead hop cursor args
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight fields)⟩ atRaw
  have rest := atCursor cellTail tail cursor args
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight fields)⟩ atRaw
  have nextValue := liftAdvance A next k prior c ty start cert current hop value atCurrent first
  have updated : Nonempty (Derivation body Γ (programGraph (updateAt A) out args)) := by
    apply compositionValue consCode ![onCursor cellTail,advanceAt A]
      out args ![tail,next] after
    intro i
    exact Fin.cases rest (Fin.cases nextValue (fun k => Fin.elim0 k)) i
  have inner := successorBranchIntro (onCursor cellGood) dead (updateAt A) out z args good updated
  let pred := pairTerm hop tail
  have nonempty := outputTransport scratchCursor cursor (suc pred) args (consEquation cursor hop tail owner) atRaw
  exact successorBranchIntro scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateAt A)) out pred args nonempty inner


#print axioms exact_OpenParameterizedConsTransition
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenConsProof
