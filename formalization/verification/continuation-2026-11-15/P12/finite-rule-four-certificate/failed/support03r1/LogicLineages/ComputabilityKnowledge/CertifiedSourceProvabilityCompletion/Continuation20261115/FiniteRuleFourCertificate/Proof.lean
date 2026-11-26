module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph
/-- One fixed actual source and one common finite fuel, before all canonical
root axioms. Every run/core/outer fuel implication is an actual source proof. -/
theorem finiteLiteralCertificate : Targets.FiniteLiteralCertificate := by
 intro logical arithmetic x pF pR c hA hn I
 let p := root pF pR logical arithmetic x
 let dt := RunProof.dispatchTag I.itag logical arithmetic x
 have hd := RunProof.dispatchInstalled p logical arithmetic x I
 obtain ⟨xt,hx⟩ := FiniteRuleFourDispatcher.InstallationProof.actualLeaf p dt logical arithmetic x hd
 obtain ⟨fuel,hfuel⟩ := FiniteRuleFourDispatcher.StatementChecks.exactFiniteLiteralDispatcher
  pF pR (verifier logical arithmetic x) c hA logical arithmetic x xt dt hn hx hd
 refine ⟨fuel,?_⟩
 intro sigma hsigma ctx larger
 obtain ⟨hdisp⟩ := hfuel sigma hsigma ctx larger .zero
 have hr := RunProof.fromDispatcher p logical arithmetic x I sigma (Term.numeral (Encodable.encode c)) larger
 obtain ⟨hrS⟩ := GorbowTheoryProofProof.monotonicity _ (S pF pR (verifier logical arithmetic x))
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hr
 have hrun := Hilbert.compose hrS hdisp
 have hc := CoreProof.fromRun p logical arithmetic x I sigma (Term.numeral (Encodable.encode c)) larger
 obtain ⟨hcS⟩ := GorbowTheoryProofProof.monotonicity _ (S pF pR (verifier logical arithmetic x))
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hc
 have hcore := Hilbert.compose hcS hrun
 have hf := FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.utag I.qctag
  (checker logical arithmetic x) I.hu I.hqc (Term.numeral (Encodable.encode c)) larger .zero
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) (Term.numeral (certificateCode sigma))
 obtain ⟨hfS⟩ := GorbowTheoryProofProof.monotonicity _ (S pF pR (verifier logical arithmetic x))
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hf
 exact ⟨⟨hrun⟩,⟨hcore⟩,⟨Hilbert.compose hfS hcore⟩⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.Proof
