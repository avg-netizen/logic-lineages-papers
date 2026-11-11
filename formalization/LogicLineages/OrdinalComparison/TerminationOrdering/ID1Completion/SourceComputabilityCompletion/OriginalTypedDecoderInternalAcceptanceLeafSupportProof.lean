module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn zRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedDecoderInternalFuelDecreaseLeafProof (choiceCases weakenProof)
open OriginalTypedDecoderInternalAcceptanceSyntaxProof OriginalTypedDecoderInternalAcceptanceStateProof
open OriginalTypedDecoderInternalAcceptanceRunProof
open OriginalTypedDecoderInternalVariableSyntaxProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem variableGraphRename {beta : Type} (out typ index gamma : OTerm alpha) (j : alpha → beta) :
    (OriginalVariableDecoder.graph out typ index gamma).relabel j =
      OriginalVariableDecoder.graph (out.relabel j) (typ.relabel j) (index.relabel j) (gamma.relabel j) := by
  simp only [OriginalVariableDecoder.graph,programRename,consTermRename,emptyRename]

theorem acceptedRejectImpossible (H : Program 1) (out : OTerm alpha)
    (hz : Nonempty (Derivation body Gamma (equal out z)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H out))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply acceptedStateCases H out _ ha
  intro beta j Delta work hj hs hw
  have hz' := renameInto hz j Delta hj
  simp only [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,zRelabel] at hz'
  exact liveZeroImpossible work
    (outputTransport InternalPairing.pairing (out.relabel j) z
      (Fin.cons (numeral 1) (Fin.cons work Fin.elim0)) hz' hs)

theorem acceptedSuccess (H : Program 1) :
    Nonempty (Derivation body Gamma (AcceptedState H (numeral 2 : OTerm alpha))) :=
  acceptedStateIntro H (numeral 2) z successPair (nilAccepted H)

theorem guardedPopForward (H : Program 1) (out suffix : OTerm alpha) (yes no : Formula alpha)
    (h : Nonempty (Derivation body Gamma
      ((yes ⊓ StepLive out suffix) ⊔ (no ⊓ equal out z))))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H out))) :
    Nonempty (Derivation body Gamma yes) := by
  apply choiceCases h
  · intro Delta inc hgood
    exact andLeft hgood
  · intro Delta inc hbad
    obtain ⟨hbot⟩ := acceptedRejectImpossible H out (andRight hbad) (weakenProof ha inc)
    exact ⟨Derivation.explosion hbot⟩

theorem variableStepAccepted (H : Program 1) (out gamma typ index suffix : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (StepVariable out gamma typ index suffix)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H out))) :
    Nonempty (Derivation body Gamma (OriginalVariableDecoder.graph (numeral 1) typ index gamma)) := by
  apply stepVariableCases out gamma typ index suffix _ h
  intro beta j Delta value hj fields
  simp only [variableGraphRename,oneRename]
  have ha' := renameInto ha j Delta hj
  rw [acceptedStateRename] at ha'
  have he := guardedPopForward H (out.relabel j) (suffix.relabel j)
    (equal value (numeral 1)) (equal value (numeral 1)).not (andRight fields) ha'
  exact outputTransport OriginalVariableDecoder.check value (numeral 1)
    (Fin.cons (typ.relabel j) (Fin.cons (index.relabel j) (Fin.cons (gamma.relabel j) Fin.elim0)))
    (by simpa only [equalEqn] using he) (andLeft fields)

theorem variableStepSuccess (gamma typ index : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma (OriginalVariableDecoder.graph (numeral 1) typ index gamma))) :
    Nonempty (Derivation body Gamma (StepVariable (numeral 2) gamma typ index z)) := by
  apply stepVariableIntro (numeral 2) gamma typ index z (numeral 1)
  apply andIntro hv
  have he : Nonempty (Derivation body Gamma (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  obtain ⟨h⟩ := andIntro he successPair
  exact ⟨InternalQuotientComparisonProof.orLeft h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafSupportProof
