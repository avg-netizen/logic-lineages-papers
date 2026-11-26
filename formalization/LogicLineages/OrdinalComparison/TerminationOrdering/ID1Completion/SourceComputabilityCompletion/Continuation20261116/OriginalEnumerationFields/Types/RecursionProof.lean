module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BothAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.ListCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.RecursionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilValue (allowed : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 allTypes (suc z) z allowed)) :=
  InternalRawListRecursionProof.nilValue (constant 1 1) allStep (suc z) (Fin.cons allowed Fin.elim0) (constantValue 1 _)

theorem consForward (raw head tail allowed : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hg : Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) allowed head ⊓ graph2 allTypes (suc z) tail allowed)) := by
  have hs := InternalRawListRecursionProof.consForward (constant 1 1) allStep raw head tail (suc z) (Fin.cons allowed Fin.elim0) hc hg
  apply InternalRawListRecursionProof.stepCases (constant 1 1) allStep (suc z) head tail (Fin.cons allowed Fin.elim0) _ hs
  intro beta j Theta old hj ht hstep
  simp only [conjunctionRename,graph2Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at ht hstep
  have hr := Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof.compositionRange contains
    ![.projection (2 : Fin 3),.projection (0 : Fin 3)] Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof.containsRange
  have hm := BothAcceptanceProof.leftOne (.composition contains ![.projection 2,.projection 0]) (.projection 1)
    ![head.relabel j,old,allowed.relabel j] hr hstep
  have hmem := binaryRecover contains (.projection 2) (.projection 0) (suc z) (allowed.relabel j) (head.relabel j)
    ![head.relabel j,old,allowed.relabel j] hm (projectionValue 2 ![head.relabel j,old,allowed.relabel j]) (projectionValue 0 ![head.relabel j,old,allowed.relabel j])
  have hv := BothAcceptanceProof.rightOne (.composition contains ![.projection 2,.projection 0]) (.projection 1)
    ![head.relabel j,old,allowed.relabel j] hr hstep
  have he := valueUnique (.projection 1) old (suc z) ![head.relabel j,old,allowed.relabel j]
    (projectionValue 1 ![head.relabel j,old,allowed.relabel j]) hv
  exact andIntro hmem (outputTransport allTypes old (suc z) ![tail.relabel j,allowed.relabel j] he ht)

theorem consBackward (raw head tail allowed : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) allowed head)))
    (ht : Nonempty (Derivation body Delta (graph2 allTypes (suc z) tail allowed))) :
    Nonempty (Derivation body Delta (graph2 allTypes (suc z) raw allowed)) := by
  have hg := binaryValue contains (.projection 2) (.projection 0) (suc z) allowed head ![head,suc z,allowed]
    hm (projectionValue 2 ![head,suc z,allowed]) (projectionValue 0 ![head,suc z,allowed])
  have hs := successorBranchIntro (.composition contains ![.projection 2,.projection 0]) (constant 3 0)
    (.projection 1) (suc z) z ![head,suc z,allowed] hg (projectionValue 1 ![head,suc z,allowed])
  exact InternalRawListRecursionProof.consValue (constant 1 1) allStep raw head tail (suc z) (suc z)
    (Fin.cons allowed Fin.elim0) hc ht hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.RecursionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.RecursionProof
