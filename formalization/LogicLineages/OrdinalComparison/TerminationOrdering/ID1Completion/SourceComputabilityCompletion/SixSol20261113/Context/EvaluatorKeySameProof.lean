module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyRelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeySameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open OriginalActiveClassKernelEqualityProof
open SixSol20261113.Erasure.EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
open UniformCertificateCompletion InternalRecursionGraphStepSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem toKey (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (left right parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (Same p H G W left right parameter))) :
 Nonempty (Derivation body Delta (keyGraph (evaluatorKey p H G W) left right parameter)) := by
 apply sameCases (baseRepresentative p H G W) left right parameter _ h
 intro beta j Theta value hj hv
 rw [keyGraphRename]
 exact keyAccept (evaluatorKey p H G W) (left.relabel j) (right.relabel j)
   (parameter.relabel j) value (andLeft hv) (andRight hv)
theorem fromKey (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (left right parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (keyGraph (evaluatorKey p H G W) left right parameter))) :
 Nonempty (Derivation body Delta (Same p H G W left right parameter)) := by
 apply programCases (evaluatorKey p H G W) (Fin.cons left (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta value hj hv
 change Nonempty (Derivation body Theta
   ((SixSol20261113.Erasure.EvaluatorErasureDefinitions.SameEvaluator
     (baseRepresentative p H G W) left right parameter).relabel j))
 rw [sameRename]
 simp only [consTermRename,emptyRename] at hv
 have hk := renameInto h j Theta hj
 rw [keyGraphRename] at hk
 exact sameIntro (baseRepresentative p H G W) (left.relabel j) (right.relabel j)
   (parameter.relabel j) value (andIntro hv
     (keyTransfer (evaluatorKey p H G W) (left.relabel j) (right.relabel j)
       (parameter.relabel j) value hk hv))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeySameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeySameProof
