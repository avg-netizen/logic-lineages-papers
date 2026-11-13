module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNonApplicationSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem notTwo (i : Fin 4) : EvaluatorOtherObserverTargets.tag i ≠ 2 := by
  unfold EvaluatorOtherObserverTargets.tag
  split <;> omega

theorem tagTestZero (input : OTerm alpha) (k n : Nat) (hne : k ≠ n)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral k) input))) :
    Nonempty (Derivation body Delta
      (programGraph (same (constructorTag (.projection 0)) (BottomRepresentative.constant n)) z (![input]))) := by
  exact OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject
    (constructorTag (.projection 0)) (BottomRepresentative.constant n)
    (numeral k) (numeral n) (![input]) ht
    (BottomSourceValidityProof.constantValue n (![input]))
    (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNe k n hne)

theorem shapeAt (input shape : OTerm alpha) (k : Nat) (hne : k ≠ 2)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral k) input)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing shape (numeral k) z))) :
    Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark shape input)) := by
  let xs : Fin 1 → OTerm alpha := ![input]
  have hz := tagTestZero input k 2 hne ht
  have hd : Nonempty (Derivation body Delta
      (programGraph OriginalConstructorShape.applicationDomain z xs)) :=
    zeroBranchIntro _ _ _ z xs hz (constantZeroValue xs)
  exact binaryValue InternalPairing.pairing OriginalConstructorShape.tag
    OriginalConstructorShape.applicationDomain shape (numeral k) z xs hp ht hd

theorem neutralAt (input : OTerm alpha) (k : Nat) (hne : k ≠ 2)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral k) input))) :
    Nonempty (Derivation body Delta (graph1 OriginalFunctionNeutrality.mark z input)) := by
  let xs : Fin 1 → OTerm alpha := ![input]
  let test : Program 1 := same (constructorTag (.projection 0)) (two 1)
  let inverse := InternalAcceptance.branch OriginalNeutralLeaf.lambdaFunctionTest
    (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)
  have hz : Nonempty (Derivation body Delta (programGraph test z xs)) := tagTestZero input k 2 hne ht
  apply InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject test inverse xs
  let A := graph1 OriginalFunctionNeutrality.mark (suc z) input
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hit := andLeft (conjunctionRecover test inverse xs ha)
  obtain ⟨he⟩ := valueUnique test (suc z) z xs hit (withHyp hz A)
  exact ⟨Derivation.implicationIntroduction (InternalTagArithmeticSupportProof.sucNeZeroApply he)⟩

theorem variableZeroAt (input : OTerm alpha) (k : Nat) (hne : k ≠ 0)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral k) input))) :
    Nonempty (Derivation body Delta (graph1 OriginalVariableRepresentative.variableMark z input)) := by
  apply OriginalVariableRepresentativeApplicationMarkProof.nonvariableMarkZero input
  let A := graph1 OriginalConstructorLeaf.variableTest (suc z) input
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz := InternalStructuralEndpointGuardSupportProof.sameRightRecover
    (constructorTag (.projection 0)) (InternalAcceptance.constantZero 1) z (![input]) ha
    (constantZeroValue (![input]))
  obtain ⟨he⟩ := valueUnique (constructorTag (.projection 0)) (numeral k) z (![input]) (withHyp ht A) hz
  exact ⟨Derivation.implicationIntroduction
    (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNeApply k 0 hne he)⟩

theorem actualShape : EvaluatorOtherObserverTargets.ActualShape := by
  intro H G M W body alpha Delta i input parameter shape _ ht hp
  exact shapeAt input shape (EvaluatorOtherObserverTargets.tag i) (notTwo i) ht hp

theorem actualNeutrality : EvaluatorOtherObserverTargets.ActualNeutrality := by
  intro H G M W body alpha Delta i input parameter _ ht
  exact neutralAt input (EvaluatorOtherObserverTargets.tag i) (notTwo i) ht

theorem actualNonvariableMark : EvaluatorOtherObserverTargets.ActualNonvariableMark := by
  intro body alpha Delta i input ht
  exact variableZeroAt input (i.val + 3) (by omega) ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverCoreProof
