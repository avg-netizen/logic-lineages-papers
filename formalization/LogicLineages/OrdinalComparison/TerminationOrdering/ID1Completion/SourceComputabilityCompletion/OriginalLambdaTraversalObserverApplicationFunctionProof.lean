module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverApplicationFunctionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaTraversalSelection OriginalLambdaTraversalObserver
open OriginalLambdaTraversalObserverSyntaxProof OriginalLambdaTraversalObserverBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Bind both ORIGINAL function observations, then instantiate the same
smaller-payload IH at each actual result. The argument is not substituted
for the function in the bottom-spine recurrence. -/
theorem atFunction (data : Data) (window : Program 1)
    (q fp arrow d e fn arg fnOut argOut input out parameter mark : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp q)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)))
    (hfp : Nonempty (Derivation body Delta (premises data window fnOut fn arrow parameter)))
    (har : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)))
    (hat : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d arg)))
    (haot : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d argOut)))
    (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
    (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut argOut))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  let qs : Fin 2 → Program 1 := ![OriginalConstructorShape.mark, BottomSpineMeasure.measure]
  let xs : Fin 1 → OTerm alpha := Fin.cons fn Fin.elim0
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [observationsRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hl' := renameInto hl j Theta hj
  unfold InternalLessThan.strictLess at hl'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hl'
  have hfr' := renameInto hfr j Theta hj
  rw [graph1Rename] at hfr'
  have hfp' := renameInto hfp j Theta hj
  rw [premisesRename] at hfp'
  have har' := renameInto har j Theta hj
  rw [graph2Rename] at har'
  have hat' := renameInto hat j Theta hj
  have haot' := renameInto haot j Theta hj
  rw [graph1Rename] at hat' haot'
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [graph4Rename] at hi' ho'
  have hroot : Nonempty (Derivation body Theta
      (graph1 OriginalConstructorShape.mark (ys 0) (fn.relabel j))) := by
    simpa only [qs,xs,Matrix.cons_val_zero,Matrix.cons_val_one,consTermRename,emptyRename] using hq 0
  have hspine : Nonempty (Derivation body Theta
      (graph1 BottomSpineMeasure.measure (ys 1) (fn.relabel j))) := by
    simpa only [qs,xs,Matrix.cons_val_zero,Matrix.cons_val_one,consTermRename,emptyRename] using hq 1
  have hri := belowPayloadApply data window (q.relabel j) (fp.relabel j)
    (fn.relabel j) (arrow.relabel j) (fnOut.relabel j) (parameter.relabel j) (ys 0)
    hb' hl' hfr' hfp'
  have hsi := belowPayloadApply data window (q.relabel j) (fp.relabel j)
    (fn.relabel j) (arrow.relabel j) (fnOut.relabel j) (parameter.relabel j) (ys 1)
    hb' hl' hfr' hfp'
  obtain ⟨hrootIff⟩ := andLeft hri
  obtain ⟨hspineIff⟩ := andLeft (andRight (andRight (andRight hsi)))
  obtain ⟨hrootProof⟩ := hroot
  obtain ⟨hspineProof⟩ := hspine
  have hrootOut : Nonempty (Derivation body Theta
      (graph1 OriginalConstructorShape.mark (ys 0) (fnOut.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hrootIff) hrootProof⟩
  have hspineOut : Nonempty (Derivation body Theta
      (graph1 BottomSpineMeasure.measure (ys 1) (fnOut.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hspineIff) hspineProof⟩
  have fi := OriginalLambdaTraversalOutputProof.invariantAtInput data window
    (fnOut.relabel j) (fn.relabel j) (arrow.relabel j) (parameter.relabel j) hfp'
  exact OriginalLambdaTraversalApplicationObserverProof.atConstructors
    (arrow.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (fnOut.relabel j) (argOut.relabel j) (input.relabel j) (out.relabel j)
    (ys 0) (ys 1) (mark.relabel j) har' (andRight (andLeft (andRight hfp')))
    hat' (andLeft (andRight fi)) haot' hi' ho' ⟨hrootProof⟩ hrootOut ⟨hspineProof⟩ hspineOut

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverApplicationFunctionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverApplicationFunctionProof
