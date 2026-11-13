module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentBranchesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem branch0 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 0) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 OriginalRootObservation.variableCase out input parameter)) := by
 apply programCases OriginalRootObservation.variableCase (Fin.cons input (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta value hj hvalue
 rw [graph2Rename]
 have ht' := renameInto ht j Theta hj
 have hv' := renameInto hv j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht' hv'
 simp only [consTermRename,emptyRename] at hvalue
 have hroot := OriginalRootObservationInternalSupportProof.dispatch0 R
   (input.relabel j) (parameter.relabel j) value ht' hvalue
 have he := valueUnique (OriginalRootObservation.rootObservation R) value (out.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hroot hv'
 exact outputTransport OriginalRootObservation.variableCase value (out.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hvalue

theorem branch3 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 3) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bottom out input parameter)) := by
 apply programCases OriginalRootObservation.bottom (Fin.cons input (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta value hj hvalue
 rw [graph2Rename]
 have ht' := renameInto ht j Theta hj
 have hv' := renameInto hv j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht' hv'
 simp only [consTermRename,emptyRename] at hvalue
 have hroot := OriginalRootObservationInternalSupportProof.dispatch3 R
   (input.relabel j) (parameter.relabel j) value ht' hvalue
 have he := valueUnique (OriginalRootObservation.rootObservation R) value (out.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hroot hv'
 exact outputTransport OriginalRootObservation.bottom value (out.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hvalue

theorem branch4 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 4) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.ordinary R) out input parameter)) := by
 apply programCases (OriginalRootObservation.ordinary R) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta value hj hvalue
 rw [graph2Rename]
 have ht' := renameInto ht j Theta hj
 have hv' := renameInto hv j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht' hv'
 simp only [consTermRename,emptyRename] at hvalue
 have hroot := OriginalRootObservationComplexSupportProof.dispatch4 R
   (input.relabel j) (parameter.relabel j) value ht' hvalue
 have he := valueUnique (OriginalRootObservation.rootObservation R) value (out.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hroot hv'
 exact outputTransport (OriginalRootObservation.ordinary R) value (out.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hvalue

theorem branch5 (R : Program 2) (input parameter out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 5) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.numbered R) out input parameter)) := by
 apply programCases (OriginalRootObservation.numbered R) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta value hj hvalue
 rw [graph2Rename]
 have ht' := renameInto ht j Theta hj
 have hv' := renameInto hv j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ht' hv'
 simp only [consTermRename,emptyRename] at hvalue
 have hroot := OriginalRootObservationComplexSupportProof.dispatch5 R
   (input.relabel j) (parameter.relabel j) value ht' hvalue
 have he := valueUnique (OriginalRootObservation.rootObservation R) value (out.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hroot hv'
 exact outputTransport (OriginalRootObservation.numbered R) value (out.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hvalue

theorem tag0 (R : Program 2) (input parameter out observedTag : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 0) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observedTag out))) :
 Nonempty (Derivation body Delta (equal observedTag (numeral 0))) := by
 have hb := branch0 R input parameter out ht hv
 have hc := EvaluatorChildrenProjectionProof.leftComponent _ _ input parameter out observedTag ho hb
 rw [equalEqn]
 exact valueUnique (OriginalRawSyntaxTransport.constant 2 0) observedTag (numeral 0) (![input,parameter]) hc
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 (![input,parameter]))

theorem tag1 (R : Program 2) (input parameter out observedTag : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observedTag out))) :
 Nonempty (Derivation body Delta (equal observedTag (numeral 1))) := by
 have hb := EvaluatorChildrenProjectionProof.lambdaBranch R input parameter out ht hv
 have hc := EvaluatorChildrenProjectionProof.leftComponent _ _ input parameter out observedTag ho hb
 rw [equalEqn]
 exact valueUnique (OriginalRawSyntaxTransport.constant 2 1) observedTag (numeral 1) (![input,parameter]) hc
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 (![input,parameter]))

theorem tag2 (R : Program 2) (input parameter out observedTag : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observedTag out))) :
 Nonempty (Derivation body Delta (equal observedTag (numeral 2))) := by
 have hb := EvaluatorChildrenProjectionProof.applicationBranch R input parameter out ht hv
 have hc := EvaluatorChildrenProjectionProof.leftComponent _ _ input parameter out observedTag ho hb
 rw [equalEqn]
 exact valueUnique (OriginalRawSyntaxTransport.constant 2 2) observedTag (numeral 2) (![input,parameter]) hc
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 2 (![input,parameter]))

theorem tag3 (R : Program 2) (input parameter out observedTag : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 3) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observedTag out))) :
 Nonempty (Derivation body Delta (equal observedTag (numeral 3))) := by
 have hb := branch3 R input parameter out ht hv
 have hc := EvaluatorChildrenProjectionProof.leftComponent _ _ input parameter out observedTag ho hb
 rw [equalEqn]
 exact valueUnique (OriginalRawSyntaxTransport.constant 2 3) observedTag (numeral 3) (![input,parameter]) hc
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 3 (![input,parameter]))

theorem tag4 (R : Program 2) (input parameter out observedTag : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 4) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observedTag out))) :
 Nonempty (Derivation body Delta (equal observedTag (numeral 4))) := by
 have hb := branch4 R input parameter out ht hv
 have hc := EvaluatorChildrenProjectionProof.leftComponent _ _ input parameter out observedTag ho hb
 rw [equalEqn]
 exact valueUnique (OriginalRawSyntaxTransport.constant 2 4) observedTag (numeral 4) (![input,parameter]) hc
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 4 (![input,parameter]))

theorem tag5 (R : Program 2) (input parameter out observedTag : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 5) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (ho : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observedTag out))) :
 Nonempty (Derivation body Delta (equal observedTag (numeral 5))) := by
 have hb := branch5 R input parameter out ht hv
 have hc := EvaluatorChildrenProjectionProof.leftComponent _ _ input parameter out observedTag ho hb
 rw [equalEqn]
 exact valueUnique (OriginalRawSyntaxTransport.constant 2 5) observedTag (numeral 5) (![input,parameter]) hc
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 5 (![input,parameter]))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentBranchesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentBranchesProof
