module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableUpperProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn suc sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof
open InternalOriginalPairingOrderArithmeticProof (withHyp weakStrictTrans)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalTwoDeletionInternalVariableArithmeticProof OriginalTwoDeletionInternalVariableRegionsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalTwoDeletionInternalVariableUpperProof OriginalTwoDeletionInternalVariableMiddleProof
theorem variableCommute (raw x a b i j upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw x)))
    (ho : Nonempty (Derivation body Delta (ltF i (suc j))))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower))) : Nonempty (Derivation body Delta (equal left right)) := by
  apply compareCases x i
  · have hxi : Nonempty (Derivation body (ltF x i :: Delta) (ltF x i)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hxj := strictWeakTrans x i j hxi (withHyp ho _)
    exact belowBoth raw a b i j x upper lower left right (withHyp hv _) hxi hxj
      (rightSuccessor x j hxj) (withHyp hu _) (withHyp hl _) (withHyp hd _) (withHyp hr _)
  · have hi : Nonempty (Derivation body (eqn x i :: Delta) (graph1 variableConstructor raw i)) :=
      headTransport variableConstructor raw x i Fin.elim0 ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
    exact atEarlier raw a b i j upper lower left right hi (withHyp ho _)
      (withHyp hu _) (withHyp hl _) (withHyp hd _) (withHyp hr _)
  · have hi : Nonempty (Derivation body (ltF i x :: Delta) (ltF i x)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := withHyp hv (ltF i x)
    have ho := withHyp ho (ltF i x)
    have hu := withHyp hu (ltF i x)
    have hl := withHyp hl (ltF i x)
    have hd := withHyp hd (ltF i x)
    have hr := withHyp hr (ltF i x)
    apply compareCases x (suc j)
    · exact middle raw a b i j x upper lower left right (withHyp hv _) (withHyp hi _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hu _) (withHyp hl _) (withHyp hd _) (withHyp hr _)
    · have hj : Nonempty (Derivation body (eqn x (suc j) :: ltF i x :: Delta)
          (graph1 variableConstructor raw (suc j))) :=
        headTransport variableConstructor raw x (suc j) Fin.elim0 ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
      exact atLater raw a b i j upper lower left right hj (withHyp ho _)
        (withHyp hu _) (withHyp hl _) (withHyp hd _) (withHyp hr _)
    · exact upperRegion raw a b i j x upper lower left right (withHyp hv _) (withHyp ho _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hu _) (withHyp hl _) (withHyp hd _) (withHyp hr _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableProof
