module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentFieldsProof
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

/-- Decode actual constructor type fields from the original recursive root observation. -/
theorem applicationAt (R : Program 2) (input parameter out data rest domain codomain : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right data out)))
 (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain data)))
 (h2 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right rest data)))
 (h3 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left codomain rest))) :
 Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain domain input parameter ⊓
   graph2 OriginalRootObservation.resultType codomain input parameter)) := by
 have hb := applicationBranch R input parameter out ht hv
 have hd := rightComponent _ _ input parameter out data h0 hb
 have hdom := leftComponent _ _ input parameter data domain h1 hd
 have hr := rightComponent _ _ input parameter data rest h2 hd
 have hcod := leftComponent _ _ input parameter rest codomain h3 hr
 exact andIntro hdom hcod

/-- Decode actual constructor type fields from the original recursive root observation. -/
theorem lambdaAt (R : Program 2) (input parameter out data rest domain codomain : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out input parameter)))
 (h0 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right data out)))
 (h1 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain data)))
 (h2 : Nonempty (Derivation body Delta (graph1 InternalUnpair.right rest data)))
 (h3 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left codomain rest))) :
 Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain domain input parameter ⊓
   graph2 OriginalRootObservation.codomain codomain input parameter)) := by
 have hb := lambdaBranch R input parameter out ht hv
 have hd := rightComponent _ _ input parameter out data h0 hb
 have hdom := leftComponent _ _ input parameter data domain h1 hd
 have hr := rightComponent _ _ input parameter data rest h2 hd
 have hcod := leftComponent _ _ input parameter rest codomain h3 hr
 exact andIntro hdom hcod

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentFieldsProof
