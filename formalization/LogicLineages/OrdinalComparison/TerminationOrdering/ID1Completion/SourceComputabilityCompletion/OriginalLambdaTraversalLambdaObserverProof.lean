module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaTraversalObserver OriginalLambdaTraversalLambdaObserverTestsProof
open OriginalLambdaTraversalLambdaObserverSpineProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Transfer the actual root mark through its two original pairing fields. -/
theorem rootTransfer (out input mark : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) out)))
    (hi : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) input)))
    (hm : Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark mark input))) :
    Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark mark out)) :=
  binaryValue InternalPairing.pairing OriginalConstructorShape.tag OriginalConstructorShape.applicationDomain
    mark (numeral 1) z (Fin.cons out Fin.elim0)
    (binaryRecover InternalPairing.pairing OriginalConstructorShape.tag OriginalConstructorShape.applicationDomain
      mark (numeral 1) z (Fin.cons input Fin.elim0) hm hi (applicationDomainZero input hi))
    ho (applicationDomainZero out ho)

theorem rootAtTags (out input mark : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) out)))
    (hi : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) input))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalConstructorShape.mark mark out).iff (graph1 OriginalConstructorShape.mark mark input))) := by
  let A := graph1 OriginalConstructorShape.mark mark out
  let B := graph1 OriginalConstructorShape.mark mark input
  obtain ⟨hf⟩ := rootTransfer input out mark (withHyp hi A) (withHyp ho A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := rootTransfer out input mark (withHyp ho B) (withHyp hi B)
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- All five ORIGINAL observers agree on every symbolic mark for literal
lambda roots. The actual spine fold is included, not a replacement test. -/
theorem atTags (out input mark : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) out)))
    (hi : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) input))) :
    Nonempty (Derivation body Delta (observations out input mark)) :=
  andIntro (rootAtTags out input mark ho hi)
    (andIntro (BottomRepresentativeInternalProof.indicatorIff OriginalVariableRepresentative.variableMark
      mark out input z z (variableZero out ho) (variableZero input hi) ⟨refl z⟩)
      (andIntro (BottomRepresentativeInternalProof.indicatorIff OriginalFunctionNeutrality.mark
        mark out input z z (neutralityZero out ho) (neutralityZero input hi) ⟨refl z⟩)
        (andIntro (BottomRepresentativeInternalProof.indicatorIff BottomSpineMeasure.measure
          mark out input z z (spineZero out ho) (spineZero input hi) ⟨refl z⟩)
          (BottomRepresentativeInternalProof.indicatorIff BottomRepresentative.bottomTest
            mark out input z z (bottomZero out ho) (bottomZero input hi) ⟨refl z⟩))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverProof
