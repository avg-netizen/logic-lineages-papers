module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorComponentsQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorParameterQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualCases (parameter : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (c gamma count : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (parameter.relabel j) c gamma)) →
   Nonempty (Derivation body Theta (OriginalContextInsertion.lengthGraph count gamma)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let len : Program 1 := .composition OriginalContextInsertion.length ![InternalUnpair.right]
 let qs : Fin 3 → Program 1 := ![InternalUnpair.left,InternalUnpair.right,len]
 apply programsCases qs (Fin.cons parameter Fin.elim0) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xx : Fin 1 → OTerm beta := Fin.cons (parameter.relabel j) Fin.elim0
 have hl := unaryRecover OriginalContextInsertion.length InternalUnpair.right (ys 2) (ys 1) xx (hq 2) (hq 1)
 have hp := InternalRecursionClosureLogicProof.closedApply
   (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body beta (parameter.relabel j) (ys 0) (ys 1))
   (andIntro (hq 0) (hq 1))
 exact next beta j Theta (ys 0) (ys 1) (ys 2) hj hp hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorParameterQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorParameterQueries
