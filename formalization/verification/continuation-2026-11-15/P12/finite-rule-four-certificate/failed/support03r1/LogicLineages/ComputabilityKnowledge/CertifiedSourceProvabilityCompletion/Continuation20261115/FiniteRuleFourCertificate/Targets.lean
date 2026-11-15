module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113
/-- Same finite literal code succeeds through actual iterator, CORE and Fuel.
One bound precedes all root axioms and all symbolic larger-fuel terms. -/
def FiniteLiteralCertificate : Prop :=
 ∀ (logical arithmetic : Program 1) (x : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (verifier logical arithmetic x) c →
 (∀ v, evaluate x v = HistoryDispatcher.axiomFunction v) →
 ∀ I : Installation (root pF pR logical arithmetic x) logical arithmetic x,
 ∃ fuel : Nat, ∀ sigma : Sentence,
 sigma ∈ GorbowPRDefiningEquations.axioms (root pF pR logical arithmetic x) →
 ∀ ctx (larger : Term ctx),
 Nonempty (Derivation (S pF pR (verifier logical arithmetic x))
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral fuel) larger)
   (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag
    (Term.numeral (Encodable.encode c)) larger (Term.numeral (certificateCode sigma)))
    (LiteralCheckerAuxiliaries.successfulState I.ptag I.ctag .zero
     (Term.numeral (rawCode sigma)) .zero .zero)))) ∧
 Nonempty (Derivation (S pF pR (verifier logical arithmetic x))
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral fuel) larger)
   (.equal (LiteralCheckerAcceptance.coreCall I.qctag
    (Term.numeral (Encodable.encode c)) larger .zero
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
    (Term.numeral (certificateCode sigma))) (.succ .zero)))) ∧
 Nonempty (Derivation (S pF pR (verifier logical arithmetic x))
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral fuel) larger)
   (SixSol20261112.Fuel.success I.utag (Term.numeral (Encodable.encode c)) larger .zero
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
    (Term.numeral (certificateCode sigma)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.Targets
