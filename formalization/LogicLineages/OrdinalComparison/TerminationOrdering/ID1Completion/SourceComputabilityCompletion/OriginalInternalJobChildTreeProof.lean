module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildGeometryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildTreeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem treeCases (child : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
  (role typ typed stored : OTerm beta), (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (child.relabel j) role typed)) →
  Nonempty (Derivation body Theta (graph2 InternalPairing.pairing typed typ stored)) →
  Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let qs : Fin 4 → Program 1 := ![InternalUnpair.left,InternalUnpair.right,leftOf InternalUnpair.right,rightOf InternalUnpair.right]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs (Fin.cons child Fin.elim0) psi
 intro beta j Theta ys hinc hq
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 1 → OTerm beta := Fin.cons (child.relabel j) Fin.elim0
 have hp := reconstructPair (child.relabel j) (ys 0) (ys 1) (hq 0) (hq 1)
 have ht := OriginalRawSyntaxTransportInternalParserSupportProof.selectorPair InternalUnpair.right (ys 1) (ys 2) (ys 3) xs (hq 1) (hq 2) (hq 3)
 exact next beta j Theta (ys 0) (ys 2) (ys 1) (ys 3) hinc hp ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildTreeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildTreeProof
