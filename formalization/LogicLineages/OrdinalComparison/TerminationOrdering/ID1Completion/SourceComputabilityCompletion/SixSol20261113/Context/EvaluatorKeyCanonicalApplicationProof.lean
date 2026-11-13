module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTagTransferProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions
open OriginalLambdaTraversalInternal
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSyntaxProof
open OriginalLambdaTraversalInternalFieldsSyntaxProof
open EvaluatorKeyCanonicalSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open InternalSquareRootArithmeticSupportProof (orderRight)

theorem atLeftFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (q left right leftOut rightOut parameter ld lc lf la fp ap : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
    (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
    (hl : Nonempty (Derivation body Delta (ApplicationFields left ld lc lf la)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp lf)))
    (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap la)))
    (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp q)))
    (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap q)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 2) right))) :
    Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
  apply OriginalLambdaTraversalApplicationOpeningProof.applicationCases right parameter _ ht
  intro beta j Theta payload arrow rd rc rfp rap rf ra hj hc _ _ _ _ _
  rw [equalRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hl' := renameInto hl j Theta hj
  rw [applicationFieldsRename] at hl'
  have hfr' := renameInto hfr j Theta hj
  have har' := renameInto har j Theta hj
  rw [graph1Rename] at hfr' har'
  have hfl' := renameInto hfl j Theta hj
  have hal' := renameInto hal j Theta hj
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hfl' hal'
  have hr := OriginalLambdaTraversalApplicationFieldsProof.fromConstructors arrow rd rc rfp rap rf ra (right.relabel j) hc
  exact EvaluatorKeyCanonicalApplicationQueriesProof.withOutputs p H G W P
    (q.relabel j) (left.relabel j) (right.relabel j) (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j)
    (ld.relabel j) (lc.relabel j) (lf.relabel j) (la.relabel j) rd rc rf ra (fp.relabel j) (ap.relabel j)
    hb' hp' hl' hr hfr' har' hfl' hal'

theorem atTag (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (q left right leftOut rightOut parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q left)))
    (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 2) left))) :
    Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
  have had := EvaluatorKeyCanonicalApplicationSupportProof.admitted p H G W P left right leftOut rightOut parameter hp
  have htRight := SixSol20261113.Erasure.EvaluatorOtherMarksTagTransferProof.actualTagTransfer
    (baseRepresentative p H G W) H G (member p H G W) W left right parameter (numeral 2) had ht
  apply OriginalLambdaTraversalApplicationOpeningProof.applicationCases left parameter _ ht
  intro beta j Theta payload arrow ld lc fp ap lf la hj hc hpr hfr har hfl hal
  rw [equalRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have htRight' := renameInto htRight j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at htRight'
  obtain ⟨he⟩ := valueUnique InternalUnpair.right payload (q.relabel j) (![left.relabel j]) hpr hr'
  obtain ⟨hfl⟩ := hfl
  obtain ⟨hal⟩ := hal
  have hl := OriginalLambdaTraversalApplicationFieldsProof.fromConstructors arrow ld lc fp ap lf la (left.relabel j) hc
  exact atLeftFields p H G W P (q.relabel j) (left.relabel j) (right.relabel j)
    (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) ld lc lf la fp ap
    hb' hp' hl hfr har ⟨orderRight fp he hfl⟩ ⟨orderRight ap he hal⟩ htRight'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationProof
