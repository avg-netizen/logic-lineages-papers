module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverTestsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaTraversalLambdaObserverTestsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual application-only spine fold treats literal lambdas as leaves;
its exact output is pair(0,0). No traversal or semantic spine replacement. -/
theorem spineZero (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure z raw)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons z Fin.elim0)
  let tag : Program 2 := leftOf (rightOf (.projection 0))
  have htag : Nonempty (Derivation body Delta (programGraph tag (numeral 1) xs)) := by
    apply programCases (rightOf (.projection (0 : Fin 1))) (Fin.cons raw Fin.elim0) _
    intro beta j Theta payload hj hp
    simp only [programRename,oneRename]
    simp only [consTermRename,emptyRename] at hp
    have ht' := renameInto ht j Theta hj
    simp only [graph1Rename,oneRename] at ht'
    let unary : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
    let binary : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons z Fin.elim0)
    have hleft := unaryRecover InternalUnpair.left (rightOf (.projection 0))
      (numeral 1) payload unary ht' hp
    have hright := unaryRecover InternalUnpair.right (.projection 0) payload (raw.relabel j) unary
      hp (projectionValue 0 unary)
    have hr := unaryValue InternalUnpair.right (.projection 0) payload (raw.relabel j) binary
      hright (projectionValue 0 binary)
    simpa only [xs,tag,binary,leftOf,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.zRelabel] using
      (unaryValue InternalUnpair.left (rightOf (.projection 0)) (numeral 1) payload binary hleft hr)
  have hne : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 3)).not) := by
    have h : Derivation body [equal (numeral 1 : OTerm alpha) (numeral 3)]
        (eqn (suc z) (suc (suc (suc z)))) := by
      simpa only [equalEqn,numeral] using
        (Derivation.hypothesis List.mem_cons_self : Derivation body
          [equal (numeral 1 : OTerm alpha) (numeral 3)] (equal (numeral 1) (numeral 3)))
    exact ⟨InternalPositiveUnfoldingSupportProof.weakenClosed
      (Derivation.implicationIntroduction (zeroNeSuc (cancelSuc h))) Delta⟩
  have htest := OriginalHereditaryValidityInternalBranchProof.sameRejectAt tag (BottomRepresentative.constant 3)
    (numeral 1) (numeral 3) xs htag (BottomSourceValidityProof.constantValue 3 xs) hne
  have hleaf : Nonempty (Derivation body Delta (graph2 BottomSpineMeasure.leaf z raw z)) :=
    binaryValue InternalPairing.pairing
      (InternalApplicationStepPeel.same tag (BottomRepresentative.constant 3)) (InternalAcceptance.constantZero 2)
      z z z xs InternalApplicationValidityStackAppendTransitionProof.pairZero htest
      (InternalAcceptanceConjunctionProof.constantZeroValue xs)
  let test := InternalApplicationStepPeel.same OriginalConstructorShape.tag (two 1)
  have hlift := unaryValue test (.projection 0) z raw xs (applicationTestZero raw ht) (projectionValue 0 xs)
  have hguard := InternalApplicationResultStackCompositionFrameConstructorsProof.conjunctionRejectLeft
    (InternalParameterizedApplicationResultStack.liftP test) (InternalLessThan.constantOne 2) xs hlift
  exact BottomSpineMeasureInternalProof.measureValue z raw
    (andRight (InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
      (InternalLessThan.constantOne 2) BottomSpineMeasure.leaf BottomSpineMeasure.combine raw z z hguard hleaf))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverSpineProof
