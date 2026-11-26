module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CoreProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalCore {n ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (rawOld arithmetic : Program 1) (x : Program 3)
 (isS : Bool) (I : Installation p f lhs rhs rawOld arithmetic x isS) (formula leftTerm index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (OriginalQuantifierLogicalExtension.guards isS I.fval formula leftTerm)
   (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero
    (.add (OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm) (OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm)) (rawCertificate I.ctag I.quantifierTag formula leftTerm)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := OriginalQuantifierLogicalExtension.guards isS I.fval formula leftTerm
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let code := CurrentQuantifierLogicalCertificate.rawCertificate I.ctag I.quantifierTag formula leftTerm
 let eq := OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm
 let it := I.coreTag+LiteralCheckerAcceptance.iteratorOffset LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x
 let run := LiteralCheckerAcceptance.runCall it I.ptag index fuel code
 obtain ⟨hrun⟩ := RunProof.internalRawSingletonRun p f lhs rhs rawOld arithmetic x isS I formula leftTerm index fuel
 obtain ⟨hf,hi⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p I.coreTag LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x I.h_coreTag
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p it I.iteratorTag 4
  (SixSol20261112.HistoryMachine.iterator (CurrentQuantifierLogicalCertificate.kernel f lhs rhs rawOld arithmetic x)) hi I.h_iteratorTag ctx
  (code ::ᵥ HistoryRunSplice.state I.ptag (.succ .zero) code ::ᵥ index ::ᵥ fuel ::ᵥ nil)
 have hstate := localTrans _ _ _ (.base hcopy) (.mp (.base hrun) hh)
 obtain ⟨hcomplete⟩ := LiteralCheckerAcceptance.CompletenessProof.completeBody p (I.coreTag+1) I.ptag I.ctag hf I.h_ptag I.h_ctag
  run .zero (.add eq eq) code eq .zero
 have hbody : Hilbert.Local T ctx G (LiteralCheckerAcceptance.WitnessProof.body I.ptag I.ctag run .zero (.add eq eq) eq .zero) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (.base (.logical (.reflexive (.add eq eq))))) hstate
 have hfinish := Hilbert.Local.mp (.base hcomplete) hbody
 obtain ⟨hnorm⟩ := LiteralCheckerAcceptance.NormalizationProof.internalCoreNormalization n p I.coreTag I.ptag
  LiteralSyntaxValidator.lineValidator (logical f lhs rhs rawOld) arithmetic x I.h_coreTag I.h_ptag ctx index fuel .zero (.add eq eq) code
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hnorm) hfinish))⟩

theorem internalFuel {n ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (rawOld arithmetic : Program 1) (x : Program 3)
 (isS : Bool) (I : Installation p f lhs rhs rawOld arithmetic x isS) (formula leftTerm index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (OriginalQuantifierLogicalExtension.guards isS I.fval formula leftTerm)
   (SixSol20261112.Fuel.success I.verifierTag index fuel .zero
    (.add (OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm) (OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm)) (rawCertificate I.ctag I.quantifierTag formula leftTerm)))) := by
 obtain ⟨hc⟩ := internalCore p f lhs rhs rawOld arithmetic x isS I formula leftTerm index fuel
 obtain ⟨hi⟩ := SixSol20261113.FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.verifierTag I.coreTag (CurrentQuantifierLogicalCertificate.checker f lhs rhs rawOld arithmetic x) I.h_verifierTag I.h_coreTag
  index fuel .zero (.add (OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm)
   (OriginalQuantifierLogicalProducers.conclusionValue isS I.ctag I.atag formula leftTerm)) (CurrentQuantifierLogicalCertificate.rawCertificate I.ctag I.quantifierTag formula leftTerm)
 let T := GorbowPRNumeralCalculation.Theory p
 let H := OriginalQuantifierLogicalExtension.guards isS I.fval formula leftTerm
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hcore := Hilbert.Local.mp (.base hc) hh
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hi) hcore))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CoreProof
