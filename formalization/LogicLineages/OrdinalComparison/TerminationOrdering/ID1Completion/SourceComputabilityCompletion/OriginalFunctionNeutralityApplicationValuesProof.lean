module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalNeutralLeaf OriginalFunctionNeutralityApplicationFieldsProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeel
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- An original application with lambda function has exactly zero neutrality
flag. The supplied tag equality is an internal arithmetic derivation. -/
theorem neutralAtLambda (d e fn arg parent tag : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 application parent d e fn arg)))
    (ht : Nonempty (Derivation body Delta (OriginalConstructorShape.tagGraph tag fn)))
    (he : Nonempty (Derivation body Delta (eqn tag (suc z)))) :
    Nonempty (Derivation body Delta (graph1 neutralTest z parent)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons parent Fin.elim0
  let inverse := InternalAcceptance.branch lambdaFunctionTest
    (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)
  have ht1 := outputTransport (leftOf (functionPayload (.projection 0))) tag (suc z) xs he
    (rawFunctionTag d e fn arg parent tag hp ht)
  have hl : Nonempty (Derivation body Delta (graph1 lambdaFunctionTest (suc z) parent)) :=
    sameAccept (leftOf (functionPayload (.projection 0))) (InternalLessThan.constantOne 1)
      (suc z) xs ht1 (InternalLessThanSupportProof.oneConstantValue xs)
  have hz : Nonempty (Derivation body Delta (programGraph inverse z xs)) :=
    successorBranchIntro lambdaFunctionTest (InternalLessThan.constantOne 1)
      (InternalAcceptance.constantZero 1) z z xs hl (constantZeroValue xs)
  apply InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject
    (same (constructorTag (.projection 0)) (two 1)) inverse xs
  let P := graph1 neutralTest (suc z) parent
  have hp1 : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hright := andRight (conjunctionRecover
    (same (constructorTag (.projection 0)) (two 1)) inverse xs hp1)
  obtain ⟨hne⟩ := valueUnique inverse (suc z) z xs hright (withHyp hz P)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hne)⟩

/-- An original application with non-lambda function has exactly one
neutrality flag. Rejection uses the existing internal equality theorem. -/
theorem neutralAtNonlambda (d e fn arg parent tag : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 application parent d e fn arg)))
    (ht : Nonempty (Derivation body Delta (OriginalConstructorShape.tagGraph tag fn)))
    (he : Nonempty (Derivation body Delta (eqn tag (suc z)).not)) :
    Nonempty (Derivation body Delta (graph1 neutralTest (suc z) parent)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons parent Fin.elim0
  have hl : Nonempty (Derivation body Delta (graph1 lambdaFunctionTest z parent)) :=
    binaryValue InternalEqualityTest.equalityTest (leftOf (functionPayload (.projection 0)))
      (InternalLessThan.constantOne 1) z tag (suc z) xs
      (InternalOriginalObjectFiberPathDispatchSupportProof.equalityOfNonmatch tag (suc z) he)
      (rawFunctionTag d e fn arg parent tag hp ht)
      (InternalLessThanSupportProof.oneConstantValue xs)
  have hinverse : Nonempty (Derivation body Delta
      (graph1 (InternalAcceptance.branch lambdaFunctionTest (InternalLessThan.constantOne 1)
        (InternalAcceptance.constantZero 1)) (suc z) parent)) :=
    zeroBranchIntro lambdaFunctionTest (InternalLessThan.constantOne 1)
      (InternalAcceptance.constantZero 1) (suc z) xs hl
      (InternalLessThanSupportProof.oneConstantValue xs)
  exact conjunctionAccept (same (constructorTag (.projection 0)) (two 1))
    (InternalAcceptance.branch lambdaFunctionTest (InternalLessThan.constantOne 1)
      (InternalAcceptance.constantZero 1)) xs
    (sameAccept (constructorTag (.projection 0)) (two 1) positionTerm xs
      (andLeft (OriginalConstructorShapeApplicationProof.rawFields d e fn arg parent hp))
      (twoValue xs)) hinverse

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationValuesProof
