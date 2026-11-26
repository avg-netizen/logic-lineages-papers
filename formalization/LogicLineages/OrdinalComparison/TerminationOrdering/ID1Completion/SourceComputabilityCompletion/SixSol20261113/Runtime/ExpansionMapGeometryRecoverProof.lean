module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryMapAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRecoverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem mapAppendRecover (F : Program 1) (left right joined mappedLeft mappedRight out : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)))
 (hl : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) mappedLeft left)))
 (hr : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) mappedRight right)))
 (ho : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) out joined))) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out mappedLeft mappedRight)) := by
 apply programCases InternalApplicationValidityStackAppend.append ![mappedLeft,mappedRight] _
 intro beta j Theta combined hinc ha
 have hx : (fun i => (![mappedLeft,mappedRight] i).relabel j) = ![mappedLeft.relabel j,mappedRight.relabel j] := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at ha
 have hj' := renameInto hj j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have ho' := renameInto ho j Theta hinc
 simp only [graph1Rename,graph2Rename] at hj' hl' hr' ho'
 have hm := SixSol20261113.Context.UnaryMapAppendProof.actualMapAppend F body beta Theta
   (left.relabel j) (right.relabel j) (joined.relabel j) (mappedLeft.relabel j) (mappedRight.relabel j) combined hj' hl' hr' ha
 have he := valueUnique (InternalListMap.map (k := 0) F) combined (out.relabel j) ![joined.relabel j] hm ho'
 rw [graph2Rename]
 exact outputTransport InternalApplicationValidityStackAppend.append combined (out.relabel j)
   ![mappedLeft.relabel j,mappedRight.relabel j] he ha

theorem reverseAppendRecover (left right joined reverseLeft reverseRight out : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reverseLeft left)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reverseRight right)))
 (ho : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse out joined))) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out reverseRight reverseLeft)) := by
 apply programCases InternalApplicationValidityStackAppend.append ![reverseRight,reverseLeft] _
 intro beta j Theta combined hinc ha
 have hx : (fun i => (![reverseRight,reverseLeft] i).relabel j) = ![reverseRight.relabel j,reverseLeft.relabel j] := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at ha
 have hj' := renameInto hj j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have ho' := renameInto ho j Theta hinc
 simp only [graph1Rename,graph2Rename] at hj' hl' hr' ho'
 have hm := SixSol20261113.Context.ReverseAppendProof.actualReverseAppend body beta Theta
   (left.relabel j) (right.relabel j) (joined.relabel j) (reverseLeft.relabel j) (reverseRight.relabel j) combined hj' hl' hr' ha
 have he := valueUnique OriginalTypedArgumentObservations.reverse combined (out.relabel j) ![joined.relabel j] hm ho'
 rw [graph2Rename]
 exact outputTransport InternalApplicationValidityStackAppend.append combined (out.relabel j)
   ![reverseRight.relabel j,reverseLeft.relabel j] he ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRecoverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRecoverProof
