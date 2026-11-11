module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDecreaseLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalTypedDecoderInternalAcceptanceCouplingSyntaxProof
open OriginalTypedDecoderInternalAcceptanceCouplingPushProof
open OriginalTypedDecoderInternalLogicSyntaxProof OriginalTypedDecoderInternalVariableSyntaxProof
open OriginalTypedDecoderInternalFuelDecreaseLeafProof

theorem orProofLeft {p q : Formula alpha} (h : Nonempty (Derivation body Delta p)) :
    Nonempty (Derivation body Delta (p ⊔ q)) := by
  obtain ⟨h⟩ := h
  exact ⟨InternalQuotientComparisonProof.orLeft h⟩

theorem orProofRight {p q : Formula alpha} (h : Nonempty (Derivation body Delta q)) :
    Nonempty (Derivation body Delta (p ⊔ q)) := by
  obtain ⟨h⟩ := h
  exact ⟨InternalQuotientComparisonProof.orRight h⟩

theorem negativeRename {beta : Type} (p : Formula alpha) (j : alpha → beta) :
    p.not.relabel j = (p.relabel j).not := rfl

theorem choiceRename {beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p ⊔ q).relabel j = (p.relabel j) ⊔ (q.relabel j) := rfl

theorem zeroEqual : Nonempty (Derivation body Delta (equal (z : OTerm alpha) (numeral 0))) := by
  rw [equalEqn]
  exact ⟨refl z⟩

theorem bottomCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepBottom out typ payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .bottom mode gamma typ tag payload rest joinedRest suffix)) := by
  apply choiceCases h
  · intro Theta inc fields
    apply pushZeroCases rest joinedRest suffix _ (weakenProof ha inc)
    intro beta j Xi fs js hj happ hfs hjs
    rw [localCoupledRename]
    have hg := renameInto (andLeft fields) j Xi hj
    simp only [conjunctionRename,equalRename,numeral,sucRelabel,zRelabel] at hg
    exact localLiveIntro H .bottom _ _ _ _ _ _ _ _
      (rest.relabel j) (joinedRest.relabel j) fs js happ hfs hjs
      (orProofLeft (andIntro hg hfs)) (orProofLeft (andIntro hg hjs))
  · intro Theta inc fields
    exact localFailureIntro H .bottom _ _ _ _ _ _ _ _
      (orProofRight (andIntro (andLeft fields) zeroEqual))
      (orProofRight (andIntro (andLeft fields) zeroEqual))

theorem nilCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepArgumentsNil out typ payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .nil mode gamma typ tag payload rest joinedRest suffix)) := by
  apply choiceCases h
  · intro Theta inc fields
    apply pushZeroCases rest joinedRest suffix _ (weakenProof ha inc)
    intro beta j Xi fs js hj happ hfs hjs
    rw [localCoupledRename]
    have hg := renameInto (andLeft fields) j Xi hj
    simp only [conjunctionRename,equalRename,numeral,sucRelabel,zRelabel] at hg
    exact localLiveIntro H .nil _ _ _ _ _ _ _ _
      (rest.relabel j) (joinedRest.relabel j) fs js happ hfs hjs
      (orProofLeft (andIntro hg hfs)) (orProofLeft (andIntro hg hjs))
  · intro Theta inc fields
    exact localFailureIntro H .nil _ _ _ _ _ _ _ _
      (orProofRight (andIntro (andLeft fields) zeroEqual))
      (orProofRight (andIntro (andLeft fields) zeroEqual))

theorem variableCoupling (H : Program 1)
    (out mode gamma typ tag payload rest joinedRest suffix : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StepVariable out gamma typ payload rest)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledLocal H .variable mode gamma typ tag payload rest joinedRest suffix)) := by
  apply stepVariableCases out gamma typ payload rest _ h
  intro beta j Theta value hj fields
  rw [localCoupledRename]
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  apply choiceCases (andRight fields)
  · intro Xi inc accepted
    apply pushZeroCases (rest.relabel j) (joinedRest.relabel j) (suffix.relabel j) _ (weakenProof ha' inc)
    intro chi k Omega fs js hk happ hfs hjs
    rw [localCoupledRename]
    have hg := renameInto (andLeft accepted) k Omega hk
    simp only [equalRename,numeral,sucRelabel,zRelabel] at hg
    have hv := renameInto (weakenProof (andLeft fields) inc) k Omega hk
    simp only [OriginalVariableDecoder.graph,programRename,consTermRename,emptyRename] at hv
    exact localLiveIntro H .variable _ _ _ _ _ _ _ _
      ((rest.relabel j).relabel k) ((joinedRest.relabel j).relabel k) fs js happ hfs hjs
      (stepVariableIntro _ _ _ _ _ (value.relabel k) (andIntro hv (orProofLeft (andIntro hg hfs))))
      (stepVariableIntro _ _ _ _ _ (value.relabel k) (andIntro hv (orProofLeft (andIntro hg hjs))))
  · intro Xi inc rejected
    exact localFailureIntro H .variable _ _ _ _ _ _ _ _
      (stepVariableIntro _ _ _ _ _ value
        (andIntro (weakenProof (andLeft fields) inc) (orProofRight (andIntro (andLeft rejected) zeroEqual))))
      (stepVariableIntro _ _ _ _ _ value
        (andIntro (weakenProof (andLeft fields) inc) (orProofRight (andIntro (andLeft rejected) zeroEqual))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingLeafProof
