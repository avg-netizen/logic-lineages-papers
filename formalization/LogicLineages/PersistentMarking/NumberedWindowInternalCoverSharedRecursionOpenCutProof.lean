module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionOpenCutProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc z)
open ID1Completion.InternalTagArithmeticSupportProof (trans congSuc addSucc addZero)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalEqualityTestProof (rejectBackwardOrder)
open ID1Completion.InternalAcceptanceBranchProof
  (zeroBranchElim zeroBranchIntro successorBranchElim successorBranchIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph binaryGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior lambdaTape)
open NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof (literalReports)
open NumberedWindowInternalAuxMeasureOpenDataProof (nodeReports)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxTape)
open NumberedWindowInternalCoverSharedRecursionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem exactTagLess : Nonempty (Derivation body Γ (ltF (numeral 2) (numeral 6))) := by
  apply actualOriginalOrderIntroduction body α Γ (numeral 2) (numeral 6) (numeral 3)
  rw [onEquality]
  let x : OTerm α := numeral 2
  have h0 := addZero (body := body) (Gamma := Γ) x
  have h1 := trans (addSucc x z) (congSuc h0)
  have h2 := trans (addSucc x (suc z)) (congSuc h1)
  have h3 := trans (addSucc x (suc (suc z))) (congSuc h2)
  have h4 := trans (addSucc x (suc (suc (suc z)))) (congSuc h3)
  exact ⟨h4⟩

private theorem readTag (tag out : OTerm α) (fields : List (OTerm α)) (xs : Fin 4 → OTerm α)
    (key : Nonempty (Derivation body Γ (programGraph currentKey (rawCons tag (packedBody fields)) xs)))
    (test : Nonempty (Derivation body Γ (programGraph equalityTest out ![tag,numeral 2]))) :
    Nonempty (Derivation body Γ (programGraph lambdaDispatch out xs)) := by
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) tag (packedBody fields)
  let n := rawCons tag (packedBody fields)
  have head := unaryGraph cellHead currentKey tag n xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩ key
  exact binaryGraph equalityTest (unaryAfter cellHead currentKey) (literal 4 2) out tag (numeral 2) xs
    test head (literalGraph 2 xs)

theorem exact_OpenCoverSharedLambdaCut : ExactOpenCoverSharedLambdaCut := by
  intro aux lam body α Γ ty q old out
  let xs := lambdaTape ty q old
  have fields := literalReports (body := body) (Γ := Γ) ty q old
  have dispatch := readTag (numeral 2) (suc z) [ty,q] xs fields.key (equalitySelf (numeral 2))
  exact ⟨successorBranchElim lambdaDispatch aux lam out z xs dispatch,
    successorBranchIntro lambdaDispatch aux lam out z xs dispatch⟩

theorem exact_OpenCoverSharedAuxCut : ExactOpenCoverSharedAuxCut := by
  intro aux lam body α Γ dom cod fn arg old out
  let xs := auxTape dom cod fn arg old
  have fields := nodeReports (body := body) (Γ := Γ) dom cod fn arg old
  have rejected := rejectBackwardOrder (numeral 6) (numeral 2) (exactTagLess (body := body) (Γ := Γ))
  have dispatch := readTag (numeral 6) z [dom,cod,fn,arg] xs fields.key rejected
  exact ⟨zeroBranchElim lambdaDispatch aux lam out xs dispatch,
    zeroBranchIntro lambdaDispatch aux lam out xs dispatch⟩

#print axioms exact_OpenCoverSharedLambdaCut
#print axioms exact_OpenCoverSharedAuxCut

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionOpenCutProof
