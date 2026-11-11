module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A literal raw tag TWO supplies all original constructor witnesses and
strict child-payload bounds. There is no validity or child-success premise. -/
theorem applicationCases (input parameter : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversal.rawTag positionTerm input)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (payload arrow d e fp ap fn arg : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg (input.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right payload (input.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right fp fn)) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right ap arg)) →
      Nonempty (Derivation body Theta (InternalLessThan.strictLess fp payload)) →
      Nonempty (Derivation body Theta (InternalLessThan.strictLess ap payload)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let test := InternalApplicationStepPeel.same
    (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1)
  have htest : Nonempty (Derivation body Delta (graph1 test (suc z) input)) :=
    sameAccept _ _ positionTerm (Fin.cons input Fin.elim0) ht (twoValue _)
  have hlift := InternalParameterizedApplicationResultStackWiringProof.liftValue
    test (suc z) input parameter htest
  have hopen : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalLessThan.constantOne 2)) (suc z) input parameter)) :=
    conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) hlift
      (InternalLessThanSupportProof.oneConstantValue _)
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (InternalLessThan.constantOne 2) input parameter psi hopen
  intro beta j Theta payload arrow d e fp ap fn arg hj hc hpr hfr har hfl hal _
  exact k beta j Theta payload arrow d e fp ap fn arg hj hc hpr hfr har hfl hal

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
