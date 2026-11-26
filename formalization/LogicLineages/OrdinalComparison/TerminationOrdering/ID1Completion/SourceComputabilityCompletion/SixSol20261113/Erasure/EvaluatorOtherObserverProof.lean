module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalGraphCompositionFunctionalityProof (renameInto)
open GuardedSourceSyntaxProof (numeralRename)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open EvaluatorOtherObserverTargets EvaluatorOtherObserverCoreProof EvaluatorOtherObserverBottomProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem tagNotThree (i : Fin 4) (hi : i.val ≠ 1) : tag i ≠ 3 := by
  unfold tag
  split <;> omega

theorem bottomZeroAt (input : OTerm alpha) (k : Nat) (hne : k ≠ 3)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral k) input))) :
    Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomTest z input)) := by
  apply OriginalApplicationSidecarBottomTestZeroProof.zeroOfNonacceptance input
  let A := BottomRepresentative.bottomGraph (suc z) input
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb := OriginalTransparentLambdaValidityInternalBottomShapeProof.bottomTag input ha
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (numeral k) (numeral 3) (![input])
    (withHyp ht A) hb
  exact ⟨Derivation.implicationIntroduction
    (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNeApply k 3 hne he)⟩

theorem actualShape : ActualShape := EvaluatorOtherObserverCoreProof.actualShape
theorem actualNeutrality : ActualNeutrality := EvaluatorOtherObserverCoreProof.actualNeutrality
theorem actualNonvariableMark : ActualNonvariableMark := EvaluatorOtherObserverCoreProof.actualNonvariableMark

theorem actualBottom : ActualBottom := by
  intro H G M W body alpha Delta i input parameter hs ht
  by_cases hi : i.val = 1
  · have ht3 : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 3) input)) := by
      simpa only [tag,hi,show (1 : Nat) ≠ 0 from by decide,ite_false] using ht
    simp only [bottomFlag,hi,ite_true]
    apply sourceBottomCode H G M W input parameter _ hs ht3
    intro beta j Theta typ hj hc
    simp only [graph1Rename,numeralRename]
    exact BottomSourceShapeProof.bottomAccept (input.relabel j) typ hc
  · simp only [bottomFlag,hi,ite_false]
    exact bottomZeroAt input (tag i) (tagNotThree i hi) ht

theorem actualSpine : ActualSpine := by
  intro H G M W body alpha Delta i input parameter spine hs ht hp
  by_cases hi : i.val = 1
  · have ht3 : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 3) input)) := by
      simpa only [tag,hi,show (1 : Nat) ≠ 0 from by decide,ite_false] using ht
    have hp1 : Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing spine (numeral 1) (numeral 0))) := by
      simpa only [bottomFlag,hi,ite_true] using hp
    apply sourceBottomCode H G M W input parameter _ hs ht3
    intro beta j Theta typ hj hc
    simp only [graph1Rename]
    have hp' := renameInto hp1 j Theta hj
    simp only [graph2Rename,numeralRename] at hp'
    have he := valueUnique InternalPairing.pairing (numeral (Nat.pair 1 0)) (spine.relabel j)
      (![numeral 1,numeral 0]) (BottomSourceClosedProof.numeralPair 1 0) hp'
    exact outputTransport BottomSpineMeasure.measure (numeral (Nat.pair 1 0)) (spine.relabel j)
      (![input.relabel j]) he (OriginalSpineNonBottomMeasureProof.bottomMeasure (input.relabel j) typ hc)
  · have hp0 : Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing spine (numeral 0) (numeral 0))) := by
      simpa only [bottomFlag,hi,ite_false] using hp
    have hm := OriginalTransparentDirectBottomNonApplicationSpineProof.tagMeasure input (numeral (tag i)) ht
      (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNe 2 (tag i) (Ne.symm (notTwo i)))
      (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNe (tag i) 3 (tagNotThree i hi))
    have he := valueUnique InternalPairing.pairing z spine (![z,z]) (BottomSourceClosedProof.numeralPair 0 0) hp0
    exact outputTransport BottomSpineMeasure.measure z spine (![input]) he hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherObserverProof
