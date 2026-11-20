module

public import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinatesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPresentationProof
open FirstOrder Language
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation ID1Completion.SourcePresentationSupportProof
open PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof PositiveArithmeticOperatorsSupportProof PositiveArithmeticSchemasProof
open TaggedArithmeticOperators
open NumberedWindowInternalPresentationTargets NumberedWindowCheckerCoordinates
open NumberedWindowCheckerCoordinatesProof (exact_ExactCoordinates)

private theorem domainTruth (p : Program 1) (context x : Nat) :
    (checkerFormula (domain p)).Realize ![context,x] ↔ DomainHolds p x := by
  rw [checkerTruth]
  change evaluate (domain p) (context ::ᵥ x ::ᵥ nil) = 1 ↔ evaluate p (x ::ᵥ nil) = 1
  rw [exact_ExactCoordinates.1 p context x]

private theorem certificateTruth (p : Program 3) (context x y : Nat) :
    (OrdinaryArithmeticQuotient.certificateGraph (suppliedCertificate p)).Realize ![context,x,y] ↔
      CertificateHolds p x y := by
  rw [OrdinaryArithmeticQuotientProof.certificateGraphTruth]
  apply exists_congr
  intro c
  change evaluate (suppliedCertificate p) (context ::ᵥ x ::ᵥ y ::ᵥ c ::ᵥ nil) = 1 ↔
    evaluate p (x ::ᵥ c ::ᵥ y ::ᵥ nil) = 1
  rw [exact_ExactCoordinates.2 p context x y c]

private theorem operatorTruth (p : Program 1) (edge : Program 3) (context : Nat) (P : Nat → Prop)
    (x : Nat) :
    realize P (accessibilityOperator (checkerFormula (domain p))
      (OrdinaryArithmeticQuotient.certificateGraph (suppliedCertificate edge))).formula ![context,x] ↔
      DomainHolds p x ∧ ∀ y, CertificateHolds edge x y → P y := by
  rw [PositiveArithmeticOperatorsProof.accessibilityOperatorTruth,domainTruth p context x]
  exact and_congr Iff.rfl (forall_congr' fun y => imp_congr (certificateTruth edge context x y) Iff.rfl)

theorem tagged : TaggedSemantics := by
  intro pI pJ pR pD context P x
  let d := data pI pJ pR pD
  have isolation := TaggedArithmeticOperatorsProof.taggedBranchIsolation
    (scalarOperator d) (multisetOperator d) P context x
  constructor
  · rw [closedPresentationTruth,isolation.1]
    exact operatorTruth pI pR context (fun y => P (tagNumber false y)) x
  · rw [closedPresentationTruth,isolation.2]
    exact operatorTruth pJ pD context (fun y => P (tagNumber true y)) x

theorem allTerms : AllTermsSemantics := by
  intro pI pJ pR pD context P
  rw [allTermsFormula,allScalarTruth]
  apply forall_congr'
  intro x
  rw [generalImpTruth,embeddingTruth]
  have hc : FirstOrder.Language.Formula.Realize
      ((checkerFormula (domain pI)).subst
        ![numeral context, (.var (.inr 0) : OrdinaryArithmetic.Term (Empty ⊕ Fin 1))])
      (Sum.elim Empty.elim (fun _ : Fin 1 => x)) ↔ DomainHolds pI x := by
    simp only [FirstOrder.Language.Formula.Realize]
    rw [BoundedFormula.realize_subst]
    have evaluation : (fun a : Fin 2 =>
        (![numeral context, (.var (.inr 0) : OrdinaryArithmetic.Term (Empty ⊕ Fin 1))] a).realize
          (Sum.elim Empty.elim (fun _ : Fin 1 => x))) = ![context,x] := by
      funext i
      exact Fin.cases (numeralTruth context _)
        (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [evaluation]
    exact domainTruth pI context x
  rw [show (data pI pJ pR pD).scalar = domain pI from rfl,
    hc,predicateTruth,PositiveArithmeticTransformsProof.tagTermTruth]
  rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalPresentationProof
