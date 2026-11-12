module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepWrapperTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalParameterizedApplicationResultStack (liftP)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal zero constructor tag cannot open the original tag-two stack. -/
theorem variableOpening (guard : Program 2) (s parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag z s))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z s parameter)) := by
  let tag : Program 1 := InternalApplicationStepPeel.constructorTag (.projection 0)
  let test : Program 1 := InternalApplicationStepPeel.same tag (two 1)
  let xs : Fin 2 → OTerm alpha := Fin.cons s (Fin.cons parameter Fin.elim0)
  let P := graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) (suc z) s parameter
  have hn : Nonempty (Derivation body Delta P.not) := by
    have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := conjunctionRecover (liftP test) guard xs hp
    have htest := InternalParameterizedApplicationResultStackWiringProof.liftRecover test
      (suc z) s parameter (andLeft hf)
    have htwo := sameRightRecover tag (two 1) (numeral 2) (Fin.cons s Fin.elim0)
      htest (twoValue (Fin.cons s Fin.elim0))
    obtain ⟨he⟩ := valueUnique tag (numeral 2) z (Fin.cons s Fin.elim0) htwo (withHyp ht P)
    exact ⟨Derivation.implicationIntroduction
      (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNeApply 2 0 (by decide) he)⟩
  exact InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject (liftP test) guard xs hn

/-- Variable leaves have original bottom-spine mark (0,0), independently
of their type, index, validity, or any native interpretation. -/
theorem variableLeaf (s parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag z s))) :
    Nonempty (Derivation body Delta (graph2 BottomSpineMeasure.leaf z s parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons s Fin.elim0) _
  intro beta j Gamma payload hj hr
  simp only [graph2Rename,zRelabel]
  have ht' := renameInto ht j Gamma hj
  simp only [graph1Rename,zRelabel] at ht'
  have hr' : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.right payload (s.relabel j))) := by
    simpa only [graph1,consTermRename,emptyRename] using hr
  let us : Fin 1 → OTerm beta := Fin.cons (s.relabel j) Fin.elim0
  let xs : Fin 2 → OTerm beta := Fin.cons (s.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hright1 := unaryValue InternalUnpair.right (.projection (0 : Fin 1)) payload
    (s.relabel j) us hr' (projectionValue 0 us)
  have hleft := unaryRecover InternalUnpair.left (rightOf (.projection (0 : Fin 1)))
    z payload us ht' hright1
  have hright2 := unaryValue InternalUnpair.right (.projection (0 : Fin 2)) payload
    (s.relabel j) xs hr' (projectionValue 0 xs)
  have htag2 := unaryValue InternalUnpair.left (rightOf (.projection (0 : Fin 2)))
    z payload xs hleft hright2
  have hf := OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject
    (leftOf (rightOf (.projection (0 : Fin 2)))) (BottomRepresentative.constant 3)
    z (numeral 3) xs htag2 (BottomSourceValidityProof.constantValue 3 xs)
    (numeralNe 0 3 (by decide))
  exact binaryValue InternalPairing.pairing
    (InternalApplicationStepPeel.same (leftOf (rightOf (.projection (0 : Fin 2))))
      (BottomRepresentative.constant 3)) (InternalAcceptance.constantZero 2)
    z z z xs (BottomSourceClosedProof.numeralPair 0 0) hf (constantZeroValue xs)

theorem variableMeasure (s : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag z s))) :
    Nonempty (Derivation body Delta (BottomSpineMeasure.graph z s)) := by
  have hf := InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    (InternalLessThan.constantOne 2) BottomSpineMeasure.leaf BottomSpineMeasure.combine
    s z z (variableOpening (InternalLessThan.constantOne 2) s z ht) (variableLeaf s z ht)
  exact BottomSpineMeasureInternalProof.measureValue z s (andRight hf)

theorem variableSpine (s t cert parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag z s))) :
    Nonempty (Derivation body Delta
      (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
        (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  let P : Formula alpha := graph1 InternalUnpair.left (suc z) z
  have hn : Nonempty (Derivation body Delta P.not) := by
    have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := pairLeft z z z (BottomSourceClosedProof.numeralPair (body := body) (Delta := P :: Delta) 0 0)
    obtain ⟨he⟩ := valueUnique InternalUnpair.left (suc z) z (Fin.cons z Fin.elim0) hp hz
    exact ⟨Derivation.implicationIntroduction (InternalTagArithmeticSupportProof.sucNeZeroApply he)⟩
  have hreject := PositiveSpineRulesProof.testReject BottomSpineMeasure.measure 0 z xs
    (variableMeasure s ht) hn
  exact zeroBranchIntro _ _ _ (suc z) xs
    (normalizeReject _ xs hreject) (InternalLessThanSupportProof.oneConstantValue xs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepSpineProof
