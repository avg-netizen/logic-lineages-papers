module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.CoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Actual core normalization and finalizer, with sorted formula-code equality
proved internally; the run premise is discharged in the finite package. -/
theorem fromRun {n ctx : Nat} (p : Program n) (logical arithmetic : Program 1) (x : Program 3)
 (I : Installation p logical arithmetic x) (sigma : Sentence) (index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel (Term.numeral (certificateCode sigma)))
   (LiteralCheckerAuxiliaries.successfulState I.ptag I.ctag .zero (Term.numeral (rawCode sigma)) .zero .zero))
  (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
   (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) (Term.numeral (certificateCode sigma))) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code : Term ctx := Term.numeral (certificateCode sigma)
 let raw : Term ctx := Term.numeral (rawCode sigma)
 let formula : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)
 let H := Formula.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel code)
  (LiteralCheckerAuxiliaries.successfulState I.ptag I.ctag .zero raw .zero .zero)
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let it := I.qctag + LiteralCheckerAcceptance.iteratorOffset LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)
 let run := LiteralCheckerAcceptance.runCall it I.ptag index fuel code
 obtain ⟨hf,hi⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p I.qctag LiteralSyntaxValidator.lineValidator
  logical arithmetic (SaturatedAxiomLeaf.saturated x) I.hqc
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p it I.itag 4
  (SixSol20261112.HistoryMachine.iterator (kernel logical arithmetic x)) hi I.hi ctx
  (code ::ᵥ HistoryRunSplice.state I.ptag (.succ .zero) code ::ᵥ index ::ᵥ fuel ::ᵥ nil)
 have hstate := localTrans _ _ _ (.base hcopy) hh
 obtain ⟨hcomplete⟩ := LiteralCheckerAcceptance.CompletenessProof.completeBody p (I.qctag+1) I.ptag I.ctag hf I.hp I.hc
  run .zero formula code raw .zero
 obtain ⟨hformula⟩ := EncodingProof.formula (ctx := ctx) T sigma
 have hbody : Hilbert.Local T ctx G (LiteralCheckerAcceptance.WitnessProof.body I.ptag I.ctag run .zero formula raw .zero) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (.base hformula)) hstate
 have hfinish := Hilbert.Local.mp (.base hcomplete) hbody
 obtain ⟨hnorm⟩ := LiteralCheckerAcceptance.NormalizationProof.internalCoreNormalization n p I.qctag I.ptag
  LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x) I.hqc I.hp ctx index fuel .zero formula code
 exact ⟨(localTrans _ _ _ (.base hnorm) hfinish).discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.CoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.CoreProof
