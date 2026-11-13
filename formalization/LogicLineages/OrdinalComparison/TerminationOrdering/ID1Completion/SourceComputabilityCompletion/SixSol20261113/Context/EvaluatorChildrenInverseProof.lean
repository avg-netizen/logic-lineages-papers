module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenInverseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorChildrenProjectionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Decode both actual recursive values from a shared application observation.
All selector premises here are operational graph facts, not semantic equalities. -/
theorem applicationAt (R : Program 2)
    (input parameter out data typedData observations fnObserved argObserved fnValue argValue fn arg : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) input parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.functionPacked fn input parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.argumentPacked arg input parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
    (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right data out)))
    (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right typedData data)))
    (h2 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right observations typedData)))
    (h3 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left fnObserved observations)))
    (h4 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argObserved observations)))
    (h5 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fnValue fnObserved)))
    (h6 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argValue argObserved))) :
    Nonempty (Derivation body Delta
      (graph2 R fnValue fn parameter ⊓ graph2 R argValue arg parameter)) := by
  have hb := applicationBranch R input parameter out ht hv
  have hd := rightComponent _ _ input parameter out data h0 hb
  have htd := rightComponent _ _ input parameter data typedData h1 hd
  have ho := rightComponent _ _ input parameter typedData observations h2 htd
  have hfo := leftComponent _ _ input parameter observations fnObserved h3 ho
  have hao := rightComponent _ _ input parameter observations argObserved h4 ho
  have hfv := rightComponent _ _ input parameter fnObserved fnValue h5 hfo
  have hav := rightComponent _ _ input parameter argObserved argValue h6 hao
  let xs : Fin 2 → OTerm alpha := ![input,parameter]
  have hp : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.parameter parameter input parameter)) :=
    projectionValue 1 xs
  exact andIntro
    (binaryRecover R OriginalRootObservation.functionPacked OriginalRootObservation.parameter fnValue fn parameter xs hfv hf hp)
    (binaryRecover R OriginalRootObservation.argumentPacked OriginalRootObservation.parameter argValue arg parameter xs hav ha hp)

/-- Decode the actual recursive body value at its actual extended parameter. -/
theorem lambdaAt (R : Program 2)
    (input parameter out data typedData observed value child childParameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.bodyPacked child input parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.childParameter childParameter input parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
    (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right data out)))
    (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right typedData data)))
    (h2 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right observed typedData)))
    (h3 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right value observed))) :
    Nonempty (Derivation body Delta (graph2 R value child childParameter)) := by
  have hb := lambdaBranch R input parameter out ht hv
  have hd := rightComponent _ _ input parameter out data h0 hb
  have htd := rightComponent _ _ input parameter data typedData h1 hd
  have ho := rightComponent _ _ input parameter typedData observed h2 htd
  have hvalue := rightComponent _ _ input parameter observed value h3 ho
  exact binaryRecover R OriginalRootObservation.bodyPacked OriginalRootObservation.childParameter value child childParameter
    (![input,parameter]) hvalue hc hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenInverseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenInverseProof
