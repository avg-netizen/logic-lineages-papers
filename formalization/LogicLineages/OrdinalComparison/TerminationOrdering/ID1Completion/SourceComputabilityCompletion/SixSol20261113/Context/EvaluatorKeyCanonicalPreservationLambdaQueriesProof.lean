module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalLambdaTraversalInternal
open UniformCertificateCompletion EvaluatorKeyPut
open EvaluatorKeyCanonicalInductionDefinitions (C)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EvaluatorKeyCanonicalPreservationInductionDefinitions
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaTraversalInternalFieldsSyntaxProof
/-- Query the actual child traversal at its literal changed parameter after
proving strict payload descent. This CPS interface adds no recursive premise. -/
theorem childCases (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q input d e child parameter childParameter : OTerm alpha) (psi : Formula alpha)
 (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
 (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter childParameter)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (childPayload childOut : OTerm beta),
   (∀ h ∈ Delta, h.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 InternalUnpair.right childPayload (child.relabel j))) →
   Nonempty (Derivation body Theta (InternalLessThan.strictLess childPayload (q.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (C p H G W P) childOut (child.relabel j) (childParameter.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalLambdaTraversalInternalPayloadLambdaProof.lambdaPayloadCases input child q _
   (andLeft (andRight (andRight (andRight hf)))) hr (andLeft hf)
 intro beta j Theta childPayload hj hchild hbound
 have hlt := OriginalLambdaTraversalInternalPayloadArithmeticProof.lambdaDescent _ _ hbound
 apply programCases (C p H G W P) (Fin.cons (child.relabel j) (Fin.cons (childParameter.relabel j) Fin.elim0)) _
 intro eta k Xi childOut hk hc
 have hchild' := renameInto hchild k Xi hk
 have hlt' := renameInto hlt k Xi hk
 rw [graph1Rename] at hchild'
 simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hlt'
 simp only [consTermRename,emptyRename] at hc
 simp only [Term.relabel_relabel] at hchild' hlt' hc
 have hh : ∀ h ∈ Delta, h.relabel (k ∘ j) ∈ Xi := by
   intro h hm
   simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition,Function.comp_def] using hk (h.relabel j) (hj h hm)
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition,Term.relabel_relabel,Function.comp_def] using
   next eta (k ∘ j) Xi (childPayload.relabel k) childOut hh hchild' hlt' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaQueriesProof
