module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutFinalGraphsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sourceToLeaf (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (input parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G (member p H G W) W) (numeral 1) input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.leafData (refined p H G W P).base (refined p H G W P).window))
        (numeral 1) input parameter)) := by
  let r := refined p H G W P
  have hfinal := EvaluatorKeyPutFinalGraphsProof.sourceToFinal p H G W P input parameter hs
  have hc := (OriginalLambdaTraversalSelectionValidityProof.finalInternalLaws r).1.2.2
    body alpha Delta (numeral 1) input parameter
  have hl := OriginalLambdaTraversalSelectionValidityProof.leafSourceCollapse r.base r.window
    body alpha Delta (numeral 1) input parameter
  exact iffBackward hl (iffForward hc hfinal)

theorem leafToSource (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (input parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.leafData (refined p H G W P).base (refined p H G W P).window))
        (numeral 1) input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalUniverseDecoder.source H G (member p H G W) W) (numeral 1) input parameter)) := by
  let r := refined p H G W P
  have hc := (OriginalLambdaTraversalSelectionValidityProof.finalInternalLaws r).1.2.2
    body alpha Delta (numeral 1) input parameter
  have hl := OriginalLambdaTraversalSelectionValidityProof.leafSourceCollapse r.base r.window
    body alpha Delta (numeral 1) input parameter
  have hf := iffBackward hc (iffForward hl hs)
  exact iffForward (EvaluatorKeyPutFinalGraphsProof.finalSource p H G W P body alpha Delta (numeral 1)
    (Fin.cons input (Fin.cons parameter Fin.elim0))) hf

theorem atType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (input out parameter typ : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (C p H G W P) out input parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
    Nonempty (Derivation body Delta (Domain p H G W out parameter)) := by
  let r := refined p H G W P
  have hparts := EvaluatorKeyDomainClosureSupportProof.factors p H G W input parameter hd
  have hs := sourceToLeaf p H G W P input parameter (andRight hparts)
  have hi := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window out input typ parameter
    (andIntro (andLeft hparts) (andIntro (andIntro hs ht) hc))
  have hout := leafToSource p H G W P out parameter (andLeft hi)
  have hw := OriginalApplicationSidecarWindowProof.windowTransfer
    (prepared p H G W).window (numeral 1) input out parameter (andLeft hparts)
  exact EvaluatorKeyDomainClosureSupportProof.assemble p H G W out parameter hw hout
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainSupportProof
