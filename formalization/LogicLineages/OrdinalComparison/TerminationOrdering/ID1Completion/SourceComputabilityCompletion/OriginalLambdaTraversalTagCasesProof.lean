module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTagCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalHereditaryValidityInternalNodeSupportProof (equalityCases weakenProof)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaTraversal OriginalLambdaTraversalInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Exhaust the two literal structural tags and their exact OTHER predicate.
This splits every raw input internally, including malformed term encodings. -/
theorem tagCases (input : OTerm alpha) (psi : Formula alpha)
    (kapp : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 rawTag (numeral 2) (input.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (klam : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 rawTag (numeral 1) (input.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j)))
    (kother : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 otherTag (numeral 1) (input.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases rawTag (Fin.cons input Fin.elim0) _
  intro beta j Theta tag hj htag
  simp only [consTermRename,emptyRename] at htag
  let xs : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
  apply equalityCases tag (numeral 2) _
  · intro Xi inc h2
    have htag' := weakenProof htag inc
    have control2 := binaryValue InternalEqualityTest.equalityTest rawTag (two 1)
      z tag (numeral 2) xs h2 htag' (twoValue xs)
    apply equalityCases tag (numeral 1) _
    · intro Omega inc2 h1
      have control1 := binaryValue InternalEqualityTest.equalityTest rawTag (InternalLessThan.constantOne 1)
        z tag (numeral 1) xs h1 (weakenProof htag' inc2) (InternalLessThanSupportProof.oneConstantValue xs)
      have hother : Nonempty (Derivation body Omega
          (graph1 otherTag (numeral 1) (input.relabel j))) :=
        zeroBranchIntro _ _ _ (numeral 1) xs (weakenProof control2 inc2)
          (zeroBranchIntro _ _ _ (numeral 1) xs control1 (InternalLessThanSupportProof.oneConstantValue xs))
      exact kother beta j Omega (fun p hp => inc2 _ (inc _ (hj p hp))) hother
    · intro Omega inc2 h1
      have control1 := binaryValue InternalEqualityTest.equalityTest rawTag (InternalLessThan.constantOne 1)
        (suc z) tag (numeral 1) xs h1 (weakenProof htag' inc2) (InternalLessThanSupportProof.oneConstantValue xs)
      have hraw := sameRightRecover rawTag (InternalLessThan.constantOne 1) (numeral 1) xs
        control1 (InternalLessThanSupportProof.oneConstantValue xs)
      exact klam beta j Omega (fun p hp => inc2 _ (inc _ (hj p hp))) hraw
  · intro Xi inc h2
    have control2 := binaryValue InternalEqualityTest.equalityTest rawTag (two 1)
      (suc z) tag (numeral 2) xs h2 (weakenProof htag inc) (twoValue xs)
    have hraw := sameRightRecover rawTag (two 1) (numeral 2) xs control2 (twoValue xs)
    exact kapp beta j Xi (fun p hp => inc _ (hj p hp)) hraw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTagCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTagCasesProof
