module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationQueriesProof
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
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSyntaxProof
open OriginalLambdaTraversalInternalFieldsSyntaxProof
open EvaluatorKeyCanonicalSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)

theorem withOutputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (q left right leftOut rightOut parameter ld lc lf la rd rc rf ra fp ap : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
    (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
    (hl : Nonempty (Derivation body Delta (ApplicationFields left ld lc lf la)))
    (hr : Nonempty (Derivation body Delta (ApplicationFields right rd rc rf ra)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp lf)))
    (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap la)))
    (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp q)))
    (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap q))) :
    Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
  let qs : Fin 4 → Program 5 := fun i => .composition (C p H G W P)
    ![.projection ⟨i.val,by omega⟩,.projection 4]
  let xs : Fin 5 → OTerm alpha := ![lf,la,rf,ra,parameter]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [equalRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hl' := renameInto hl j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [applicationFieldsRename] at hl' hr'
  have hfr' := renameInto hfr j Theta hj
  have har' := renameInto har j Theta hj
  rw [graph1Rename] at hfr' har'
  have hfl' := renameInto hfl j Theta hj
  have hal' := renameInto hal j Theta hj
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hfl' hal'
  let xx : Fin 5 → OTerm beta := fun a => (xs a).relabel j
  have hg (i : Fin 4) : Nonempty (Derivation body Theta
      (graph2 (C p H G W P) (ys i) ((xs ⟨i.val,by omega⟩).relabel j) (parameter.relabel j))) := by
    apply compositionRecover (C p H G W P) ![.projection ⟨i.val,by omega⟩,.projection 4]
      (ys i) xx (Fin.cons ((xs ⟨i.val,by omega⟩).relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (hq i)
    intro a
    exact Fin.cases (projectionValue ⟨i.val,by omega⟩ xx)
      (Fin.cases (projectionValue 4 xx) (fun k => Fin.elim0 k)) a
  exact EvaluatorKeyCanonicalApplicationCoreProof.atOutputs p H G W P
    (q.relabel j) (left.relabel j) (right.relabel j) (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j)
    (ld.relabel j) (lc.relabel j) (lf.relabel j) (la.relabel j) (rd.relabel j) (rc.relabel j) (rf.relabel j) (ra.relabel j)
    (fp.relabel j) (ap.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    hb' hp' hl' hr' hfr' har' hfl' hal' (hg 0) (hg 1) (hg 2) (hg 3)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationQueriesProof
