module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankApplicationChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSupportProof (refl)
open OriginalLambdaTraversalSelection OriginalFinalGuardedRankObserverProof
open OriginalFinalGuardedRankSyntaxProof OriginalFinalGuardedRankBindingProof
open OriginalRawSyntaxTransport (variableRankPackedRaw)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atChildren (data : Data) (window : Program 1)
    (q fp ap arrow d e fn arg fnOut argOut input out parameter mark : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp q)))
    (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap q)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)))
    (hfp : Nonempty (Derivation body Delta (premises data window fnOut fn arrow parameter)))
    (hap : Nonempty (Derivation body Delta (premises data window argOut arg d parameter)))
    (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
    (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut argOut))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  let f : Program 2 := .composition variableRankPackedRaw (fun _ : Fin 1 => .projection 0)
  let a : Program 2 := .composition variableRankPackedRaw (fun _ : Fin 1 => .projection 1)
  let sum : Program 2 := .composition InternalArithmeticPrograms.addition ![f,a]
  let qs : Fin 3 → Program 2 := ![f,a,sum]
  let xs : Fin 2 → OTerm alpha := ![fn,arg]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [observationsRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hfl' := renameInto hfl j Theta hj
  have hal' := renameInto hal j Theta hj
  unfold InternalLessThan.strictLess at hfl' hal'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hfl' hal'
  have hfr' := renameInto hfr j Theta hj
  have har' := renameInto har j Theta hj
  rw [graph1Rename] at hfr' har'
  have hfp' := renameInto hfp j Theta hj
  have hap' := renameInto hap j Theta hj
  rw [premisesRename] at hfp' hap'
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [graph4Rename] at hi' ho'
  let xx : Fin 2 → OTerm beta := ![fn.relabel j,arg.relabel j]
  have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
    intro i
    simpa only [xs,xx,consTermRename,emptyRename] using hq i
  have hfn := unaryRecover variableRankPackedRaw (.projection 0) (ys 0) (fn.relabel j) xx
    (hq' 0) (projectionValue 0 xx)
  have harg := unaryRecover variableRankPackedRaw (.projection 1) (ys 1) (arg.relabel j) xx
    (hq' 1) (projectionValue 1 xx)
  have hsum := binaryRecover InternalArithmeticPrograms.addition f a (ys 2) (ys 0) (ys 1) xx
    (hq' 2) (hq' 0) (hq' 1)
  obtain ⟨hfi⟩ := belowPayloadApply data window (q.relabel j) (fp.relabel j) (fn.relabel j)
    (arrow.relabel j) (fnOut.relabel j) (parameter.relabel j) (ys 0) hb' hfl' hfr' hfp'
  obtain ⟨hai⟩ := belowPayloadApply data window (q.relabel j) (ap.relabel j) (arg.relabel j)
    (d.relabel j) (argOut.relabel j) (parameter.relabel j) (ys 1) hb' hal' har' hap'
  obtain ⟨hfn⟩ := hfn
  obtain ⟨harg⟩ := harg
  have hfout : Nonempty (Derivation body Theta (graph1 variableRankPackedRaw (ys 0) (fnOut.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hfi) hfn⟩
  have haout : Nonempty (Derivation body Theta (graph1 variableRankPackedRaw (ys 1) (argOut.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hai) harg⟩
  have hin := OriginalFinalGuardedRankConstructorProof.applicationValue (input.relabel j)
    (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j) (ys 0) (ys 1) (ys 2) hi' ⟨hfn⟩ ⟨harg⟩ hsum
  have hout := OriginalFinalGuardedRankConstructorProof.applicationValue (out.relabel j)
    (d.relabel j) (e.relabel j) (fnOut.relabel j) (argOut.relabel j) (ys 0) (ys 1) (ys 2) ho' hfout haout hsum
  exact BottomRepresentativeInternalProof.indicatorIff variableRankPackedRaw (mark.relabel j)
    (out.relabel j) (input.relabel j) (ys 2) (ys 2) hout hin ⟨refl (ys 2)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankApplicationChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankApplicationChildrenProof
