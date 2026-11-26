module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceClosedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomMeasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The original symbolic bottom constructor has the literal leaf mark (1,0).
The type and parameter remain arbitrary object-language terms. -/
theorem bottomLeaf (input typ parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode input typ))) :
    Nonempty (Derivation body Gamma
      (graph2 BottomSpineMeasure.leaf (numeral (Nat.pair 1 0)) input parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro β j Delta payload hj hr
  simp only [graph2Rename,numeralRename]
  have hc' := renameInto hc j Delta hj
  rw [graph1Rename] at hc'
  have hr' : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right payload (input.relabel j))) := by
    simpa only [graph1,consTermRename,emptyRename] using hr
  let xs : Fin 2 → OTerm β := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  let us : Fin 1 → OTerm β := Fin.cons (input.relabel j) Fin.elim0
  have htag := BottomSourceValidityProof.bottomConstructorTag (input.relabel j) (typ.relabel j) hc'
  have hright1 := unaryValue InternalUnpair.right (.projection (0 : Fin 1)) payload
    (input.relabel j) us hr' (projectionValue 0 us)
  have hleft := unaryRecover InternalUnpair.left (rightOf (.projection (0 : Fin 1)))
    (numeral 3) payload us htag hright1
  have hright2 := unaryValue InternalUnpair.right (.projection (0 : Fin 2)) payload
    (input.relabel j) xs hr' (projectionValue 0 xs)
  have htag2 := unaryValue InternalUnpair.left (rightOf (.projection (0 : Fin 2)))
    (numeral 3) payload xs hleft hright2
  have hf := sameAccept (leftOf (rightOf (.projection (0 : Fin 2))))
    (BottomRepresentative.constant 3) (numeral 3) xs htag2
    (BottomSourceValidityProof.constantValue 3 xs)
  exact binaryValue InternalPairing.pairing
    (InternalApplicationStepPeel.same (leftOf (rightOf (.projection (0 : Fin 2))))
      (BottomRepresentative.constant 3)) (InternalAcceptance.constantZero 2)
    (numeral (Nat.pair 1 0)) (suc z) z xs
    (BottomSourceClosedProof.numeralPair 1 0) hf (constantZeroValue xs)

/-- Actual full measure evaluation at a symbolic original bottom uses the
existing certified closed-leaf fold rule; no numerical reflection is used. -/
theorem bottomMeasure (input typ : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode input typ))) :
    Nonempty (Derivation body Gamma
      (BottomSpineMeasure.graph (numeral (Nat.pair 1 0)) input)) := by
  have hopen := BottomSourceValidityProof.bottomOpeningZero (InternalLessThan.constantOne 2)
    input typ z hc
  have hleaf := bottomLeaf input typ z hc
  have hfold := InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    (InternalLessThan.constantOne 2) BottomSpineMeasure.leaf BottomSpineMeasure.combine
    input (numeral (Nat.pair 1 0)) z hopen hleaf
  exact BottomSpineMeasureInternalProof.measureValue (numeral (Nat.pair 1 0)) input (andRight hfold)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomMeasureProof
