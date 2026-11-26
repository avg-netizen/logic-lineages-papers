module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationCoreProof
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

theorem atOutputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (q left right leftOut rightOut parameter ld lc lf la rd rc rf ra fp ap fOut aOut rfOut raOut : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
    (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
    (hl : Nonempty (Derivation body Delta (ApplicationFields left ld lc lf la)))
    (hr : Nonempty (Derivation body Delta (ApplicationFields right rd rc rf ra)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp lf)))
    (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap la)))
    (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp q)))
    (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap q)))
    (hf : Nonempty (Derivation body Delta (graph2 (C p H G W P) fOut lf parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (C p H G W P) aOut la parameter)))
    (hrf : Nonempty (Derivation body Delta (graph2 (C p H G W P) rfOut rf parameter)))
    (hra : Nonempty (Derivation body Delta (graph2 (C p H G W P) raOut ra parameter))) :
    Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
  have hc := EvaluatorKeyCanonicalApplicationSupportProof.children p H G W P
    left right leftOut rightOut parameter ld lc lf la rd rc rf ra hp hl hr
  have hfn := andLeft hc
  have harg := andRight hc
  have heF := EvaluatorKeyCanonicalBindingProof.belowPayloadApply p H G W P q fp lf rf fOut rfOut parameter
    hb hfl hfr (andIntro (andLeft hfn) (andIntro (andLeft (andRight hfn))
      (andIntro (andRight (andRight hfn)) (andIntro hf hrf))))
  have heA := EvaluatorKeyCanonicalBindingProof.belowPayloadApply p H G W P q ap la ra aOut raOut parameter
    hb hal har (andIntro (andLeft harg) (andIntro (andLeft (andRight harg))
      (andIntro (andRight (andRight harg)) (andIntro ha hra))))
  have had := EvaluatorKeyCanonicalApplicationSupportProof.admitted p H G W P left right leftOut rightOut parameter hp
  have htypes := EvaluatorAlignmentProof.actualApplication (baseRepresentative p H G W) H G (member p H G W) W
    body alpha Delta left right parameter ld lc lf la rd rc rf ra had hl hr
  let r := refined p H G W P
  have hol := OriginalLambdaTraversalInternalApplicationProof.applicationForward
    (OriginalLambdaTraversalSelection.leaf r.base r.window) left ld lc lf la parameter fOut aOut leftOut
    hl hf ha (andLeft (andRight (andRight (andRight hp))))
  have hor := OriginalLambdaTraversalInternalApplicationProof.applicationForward
    (OriginalLambdaTraversalSelection.leaf r.base r.window) right rd rc rf ra parameter rfOut raOut rightOut
    hr hrf hra (andRight (andRight (andRight (andRight hp))))
  exact EvaluatorKeyCanonicalApplicationSupportProof.rebuilt ld lc fOut aOut rd rc rfOut raOut leftOut rightOut
    (andLeft htypes) (andRight htypes) heF heA hol hor
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalApplicationCoreProof
