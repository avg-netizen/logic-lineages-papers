module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSingletonSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalStructuralEndpointGuardSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalNodeSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem singletonWeight (work frame raw parameter payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (WorkCons work frame z)))
    (hf : Nonempty (Derivation body Delta (FrameGraph frame raw parameter)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Delta (WorkFuelGraph (suc payload) work)) :=
  outputTransport workFuel (add (suc payload) z) (suc payload) (Fin.cons work Fin.elim0)
    ⟨addZero (suc payload)⟩
    (consValue work frame z (suc payload) z hc (frameValue frame raw parameter payload hf hp) nilValue)

 theorem initialAtSingleton (state work frame raw parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateGraph state (numeral 1) work)))
    (hc : Nonempty (Derivation body Delta (WorkCons work frame z)))
    (hf : Nonempty (Derivation body Delta (FrameGraph frame raw parameter))) :
    Nonempty (Derivation body Delta (graph2 initial state raw parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  let frameProgram : Program 2 := pairOf (.projection 0) (.projection 1)
  let workProgram : Program 2 := consOf frameProgram (InternalAcceptance.constantZero 2)
  have hframe := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    frame raw parameter xs hf (projectionValue 0 xs) (projectionValue 1 xs)
  have hwork := binaryValue InternalListCodec.consCode frameProgram (InternalAcceptance.constantZero 2)
    work frame z xs hc hframe (InternalLessThanSupportProof.zeroConstantValue xs)
  exact binaryValue InternalPairing.pairing (InternalLessThan.constantOne 2) workProgram
    state (numeral 1) work xs hs (InternalLessThanSupportProof.oneConstantValue xs) hwork

 theorem finishedSuccess :
    Nonempty (Derivation body Delta (graph1 finished (numeral 1 : OTerm alpha) (numeral 2))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons (numeral 2) Fin.elim0
  exact conjunctionAccept _ _ xs
    (exactAccept status xs (pairLeft (numeral 2) (numeral 1) z successPair))
    (InternalApplicationStepPeelSupportProof.sameAccept work (InternalAcceptance.constantZero 1) z xs
      (pairRight (numeral 2) (numeral 1) z successPair) (InternalLessThanSupportProof.zeroConstantValue xs))

 theorem finishedAcceptedState (state : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 finished (numeral 1) state))) :
    Nonempty (Derivation body Delta (eqn state (numeral 2))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have h := conjunctionRecover (exactOne status)
    (InternalApplicationStepPeel.same work (InternalAcceptance.constantZero 1)) xs hf
  have hs := exactRecover status xs (andLeft h)
  have hw := sameRightRecover work (InternalAcceptance.constantZero 1) z xs (andRight h)
    (InternalLessThanSupportProof.zeroConstantValue xs)
  exact valueUnique InternalPairing.pairing state (numeral 2)
    (Fin.cons (numeral 1) (Fin.cons z Fin.elim0))
    (reconstructPair state (numeral 1) z hs hw) successPair

 theorem validatorRunSuccess (s t m : Program 2) (raw parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (validator s t m) (numeral 1) raw parameter))) :
    Nonempty (Derivation body Delta (graph2 (run s t m) (numeral 2) raw parameter)) := by
  apply programCases (run s t m) (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta result hj hr
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hr
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename,oneRename] at hv'
  have hf := unaryRecover finished (run s t m) (numeral 1) result
    (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hv' hr
  exact outputTransport (run s t m) result (numeral 2)
    (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (finishedAcceptedState result hf) hr

 theorem runSuccessValidator (s t m : Program 2) (raw parameter : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (run s t m) (numeral 2) raw parameter))) :
    Nonempty (Derivation body Delta (graph2 (validator s t m) (numeral 1) raw parameter)) :=
  unaryValue finished (run s t m) (numeral 1) (numeral 2)
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) finishedSuccess hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSingletonSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSingletonSupportProof
