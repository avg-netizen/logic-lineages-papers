module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeApplicationMarkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverTestsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof
open InternalBetaTotalityProof (addHyp)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal lambda tags reject the actual tag-two equality test. -/
theorem applicationTestZero (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Delta
      (graph1 (InternalApplicationStepPeel.same OriginalConstructorShape.tag (two 1)) z raw)) :=
  OriginalHereditaryValidityInternalBranchProof.sameRejectAt OriginalConstructorShape.tag (two 1)
    (numeral 1) (numeral 2) (Fin.cons raw Fin.elim0) ht (twoValue (Fin.cons raw Fin.elim0))
    OriginalHereditaryValidityInternalBranchProof.oneNotTwo

theorem applicationDomainZero (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.applicationDomain z raw)) :=
  zeroBranchIntro _ _ _ z (Fin.cons raw Fin.elim0) (applicationTestZero raw ht)
    (constantZeroValue (Fin.cons raw Fin.elim0))

theorem variableRejected (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph1 OriginalConstructorLeaf.variableTest (numeral 1) raw).not) := by
  let V := graph1 OriginalConstructorLeaf.variableTest (numeral 1) raw
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  have hz := sameRightRecover (InternalApplicationStepPeel.constructorTag (.projection 0))
    (InternalAcceptance.constantZero 1) z xs
    (show Nonempty (Derivation body (V :: Delta) V) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (constantZeroValue xs)
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (numeral 1) z xs (withHyp ht V) hz
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem variableZero (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph1 OriginalVariableRepresentative.variableMark z raw)) :=
  OriginalVariableRepresentativeApplicationMarkProof.nonvariableMarkZero raw (variableRejected raw ht)

theorem neutralityZero (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph1 OriginalFunctionNeutrality.mark z raw)) := by
  let P := InternalApplicationStepPeel.same (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1)
  let Q := InternalAcceptance.branch OriginalNeutralLeaf.lambdaFunctionTest
    (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)
  let N := graph1 OriginalFunctionNeutrality.mark (numeral 1) raw
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  have hn : Nonempty (Derivation body Delta N.not) := by
    have h : Nonempty (Derivation body (N :: Delta) N) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp := andLeft (conjunctionRecover P Q xs h)
    have htwo := sameRightRecover (InternalApplicationStepPeel.constructorTag (.projection 0))
      (two 1) (numeral 2) xs hp (twoValue xs)
    obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (numeral 1) (numeral 2) xs
      (withHyp ht N) htwo
    exact ⟨Derivation.implicationIntroduction (zeroNeSuc (cancelSuc he))⟩
  exact OriginalTransparentLambdaValidityInternalBranchSupportProof.conjunctionReject P Q xs hn

/-- Exact bottom acceptance would force tag three, contradicting literal one.
This uses the actual exact-bottom test, including its same-type check. -/
theorem bottomRejected (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (numeral 1) raw).not) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Theta typ hj htyp
  change Nonempty (Derivation body Theta
    (((BottomRepresentative.bottomGraph (suc z) raw).not).relabel j))
  rw [BottomApplicationProof.notBottomRename]
  simp only [consTermRename,emptyRename] at htyp
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,oneRename] at ht'
  let B := BottomRepresentative.bottomGraph (numeral 1) (raw.relabel j)
  have hbottom := BottomSourceShapeProof.bottomRecover (raw.relabel j) typ (withHyp htyp B)
    (show Nonempty (Derivation body (B :: Theta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hthree := BottomSourceValidityProof.bottomConstructorTag (raw.relabel j) typ hbottom
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (numeral 1) (numeral 3)
    (Fin.cons (raw.relabel j) Fin.elim0) (withHyp ht' B) hthree
  exact ⟨Derivation.implicationIntroduction (zeroNeSuc (cancelSuc he))⟩

theorem bottomZero (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomTest z raw)) :=
  OriginalApplicationSidecarBottomTestZeroProof.zeroOfNonacceptance raw (bottomRejected raw ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverTestsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverTestsProof
