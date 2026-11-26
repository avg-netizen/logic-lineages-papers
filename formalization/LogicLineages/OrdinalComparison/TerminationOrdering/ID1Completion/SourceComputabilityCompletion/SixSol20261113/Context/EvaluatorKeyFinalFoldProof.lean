module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft)
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem toCanonical (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (out input parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
 (hf : Nonempty (Derivation body Delta (graph2 (EvaluatorKeyFinalFoldDefinitions.fold p H G W P) out input parameter))) :
 Nonempty (Derivation body Delta
   (graph2 (OriginalLambdaTraversalSelection.canonical (refined p H G W P).base (refined p H G W P).window) out input parameter)) := by
 apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
 intro beta j Theta typ hj ht
 have hd' := renameInto hd j Theta hj
 have hf' := renameInto hf j Theta hj
 simp only [Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
 rw [graph2Rename] at hf' ⊢
 simp only [consTermRename,emptyRename] at ht
 obtain ⟨law⟩ := andLeft (EvaluatorKeyFinalFoldBridgeProof.atType p H G W P
   (out.relabel j) (input.relabel j) typ (parameter.relabel j) hd' ht)
 obtain ⟨hf'⟩ := hf'
 exact ⟨Derivation.implicationElimination law hf'⟩
theorem actualFinalFoldEquality : EvaluatorKeyFinalFoldTargets.ActualFinalFoldEquality := by
 intro p H G W P body alpha Delta left right leftOut rightOut parameter dl dr same fl fr
 exact EvaluatorKeyCanonicalProof.actualCanonicalEquality p H G W P body alpha Delta
   left right leftOut rightOut parameter dl dr same
   (toCanonical p H G W P leftOut left parameter dl fl)
   (toCanonical p H G W P rightOut right parameter dr fr)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldProof
