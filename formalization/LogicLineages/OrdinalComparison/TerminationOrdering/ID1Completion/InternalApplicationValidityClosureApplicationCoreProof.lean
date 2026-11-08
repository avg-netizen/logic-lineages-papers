module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureFuelProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalApplicationValidityStackAppend InternalPairingSumBounds
open InternalApplicationValidityClosureBridgeProof InternalApplicationValidityClosureFuelProof
open InternalApplicationValidityClosureFrameProof InternalApplicationValidityStackAppendProof
open InternalApplicationValidityStackAppendListProof InternalApplicationValidityStackAppendRunProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalApplicationValidityStackInternalProof InternalControlGraphSupportProof
open InternalSourceInversionSupportProof InternalNumericIterationProof
open InternalRecursionClosureLogicProof
open InternalPairingSumBoundsProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- All auxiliary numeric values are internal constructor witnesses. Neither
the actual fuel bound nor successful parent validation is a hypothesis. -/
theorem applicationAtValues (node leaf : Program 1)
    (d e fp ap arrow fn arg parent children middle payload
      fnWork argWork joined parentWork parentState expandedState : OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hchildren : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing children fp ap)))
    (hmiddle : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing middle d children)))
    (hpayload : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing payload successState middle)))
    (hparentPair : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parent e payload)))
    (hfnWork : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode fnWork fn z)))
    (hargWork : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode argWork arg z)))
    (hjoined : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode joined fn argWork)))
    (hparentWork : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode parentWork parent z)))
    (hparentState : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing parentState (suc z) parentWork)))
    (hexpandedState : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing expandedState (suc z) joined)))
    (hnode : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hfnValid : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) fn)))
    (hargValid : Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) arg))) :
    Nonempty (Derivation body Gamma (graph1 (validator node leaf) (suc z) parent)) := by
  obtain ⟨hfiff⟩ := closedApply
    (actualOriginalValidatorSingletonSuccess body node leaf α fn fp fnWork)
    (andIntro (pairRight fn arrow fp hfn) hfnWork)
  obtain ⟨haiff⟩ := closedApply
    (actualOriginalValidatorSingletonSuccess body node leaf α arg ap argWork)
    (andIntro (pairRight arg d ap harg) hargWork)
  obtain ⟨hfnValid⟩ := hfnValid
  obtain ⟨hargValid⟩ := hargValid
  have hfirst : Nonempty (Derivation body Gamma (successfulWork node leaf (suc fp) fnWork)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hfiff) hfnValid⟩
  have hsecond : Nonempty (Derivation body Gamma (successfulWork node leaf (suc ap) argWork)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft haiff) hargValid⟩
  have happend := consBackward fnWork fn z argWork argWork joined hfnWork
    (appendZeroValue argWork) hjoined
  have hboth := successfulAppend node leaf (suc fp) (suc ap) fnWork argWork joined
    happend hfirst hsecond
  have hrun := successfulWorkAt node leaf (childFuelSum fp ap) joined expandedState
    hexpandedState hboth
  have hpush := pushBackward node leaf d e fp ap z parentState expandedState
    (applicationFrameValue d e fp ap parent parentWork parentState hparent hparentWork hparentState)
    hnode
    (expandedFrameValue d e fp ap arrow fn arg argWork joined expandedState
      harrow hfn harg hargWork hjoined hexpandedState)
  have hshort := successfulWorkIntro node leaf (suc (childFuelSum fp ap)) parentWork parentState
    hparentState
    (frontSuccBackward (transition node leaf) (childFuelSum fp ap)
      successState parentState expandedState hpush hrun)
  have hbound := closedApply
    (actualOriginalApplicationParentFuelBound body α payload middle children d fp ap)
    (andIntro hpayload (andIntro hmiddle hchildren))
  have hfull := successAtBound node leaf (suc (childFuelSum fp ap)) (suc payload) parentWork
    hbound hshort
  obtain ⟨hpiff⟩ := closedApply
    (actualOriginalValidatorSingletonSuccess body node leaf α parent payload parentWork)
    (andIntro (pairRight parent e payload hparentPair) hparentWork)
  obtain ⟨hfull⟩ := hfull
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hpiff) hfull⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationCoreProof
