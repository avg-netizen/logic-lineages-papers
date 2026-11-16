module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceAxiomSeed.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- One finite seed bound precedes every actual current-root axiom and symbolic
runtime fuel. The literal original axiomLine code is derived at the SAME current
CORE/Fuel tags; neither seed success nor source inclusion is assumed. -/
def InternalCurrentSeed : Prop :=
 ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativeUniformRule12Source.verifier f lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativeUniformRule12Registry.JointInstallation
  (CumulativeUniformRule12Source.root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ sigma : Sentence,
 sigma ∈ GorbowPRDefiningEquations.axioms
  (CumulativeUniformRule12Source.root f lhs rhs pF pR old a baseX) →
 ∀ ctx (larger : Term ctx),
 Nonempty (Derivation (S pF pR (CumulativeUniformRule12Source.verifier f lhs rhs old a baseX))
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) larger)
   (.conj
    (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag
     (Term.numeral (Encodable.encode c)) larger .zero
     (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
     (Term.numeral (FiniteRuleFourCertificate.certificateCode sigma))) (.succ .zero))
    (SixSol20261112.Fuel.success I.current.verifierTag
     (Term.numeral (Encodable.encode c)) larger .zero
     (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
     (Term.numeral (FiniteRuleFourCertificate.certificateCode sigma))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceAxiomSeed.Targets
