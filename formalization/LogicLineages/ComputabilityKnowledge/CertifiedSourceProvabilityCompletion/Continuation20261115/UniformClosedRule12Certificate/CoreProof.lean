module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.CoreProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalCore {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x) (formula leftTerm rightTerm index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedRule12.guards I.fval I.vtag formula leftTerm rightTerm)
   (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero
    (.add (UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm) (UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm)) (certificate I.ctag I.constructorTag formula leftTerm rightTerm)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := UniformClosedRule12.guards I.fval I.vtag formula leftTerm rightTerm
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let code := UniformClosedRule12Certificate.certificate I.ctag I.constructorTag formula leftTerm rightTerm
 let eq := UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm
 let it := I.coreTag+LiteralCheckerAcceptance.iteratorOffset LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x
 let run := LiteralCheckerAcceptance.runCall it I.ptag index fuel code
 obtain ⟨hrun⟩ := RunProof.internalSingletonRun p old arithmetic x I formula leftTerm rightTerm index fuel
 obtain ⟨hf,hi⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p I.coreTag LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x I.h_core
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p it I.iteratorTag 4
  (SixSol20261112.HistoryMachine.iterator (UniformClosedRule12Certificate.kernel old arithmetic x)) hi I.h_iterator ctx
  (code ::ᵥ HistoryRunSplice.state I.ptag (.succ .zero) code ::ᵥ index ::ᵥ fuel ::ᵥ nil)
 have hstate := localTrans _ _ _ (.base hcopy) (.mp (.base hrun) hh)
 obtain ⟨hcomplete⟩ := LiteralCheckerAcceptance.CompletenessProof.completeBody p (I.coreTag+1) I.ptag I.ctag hf I.h_ptag I.h_ctag
  run .zero (.add eq eq) code eq .zero
 have hbody : Hilbert.Local T ctx G (LiteralCheckerAcceptance.WitnessProof.body I.ptag I.ctag run .zero (.add eq eq) eq .zero) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (.base (.logical (.reflexive (.add eq eq))))) hstate
 have hfinish := Hilbert.Local.mp (.base hcomplete) hbody
 obtain ⟨hnorm⟩ := LiteralCheckerAcceptance.NormalizationProof.internalCoreNormalization n p I.coreTag I.ptag
  LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x I.h_core I.h_ptag ctx index fuel .zero (.add eq eq) code
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hnorm) hfinish))⟩

theorem internalFuel {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x) (formula leftTerm rightTerm index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedRule12.guards I.fval I.vtag formula leftTerm rightTerm)
   (SixSol20261112.Fuel.success I.verifierTag index fuel .zero
    (.add (UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm) (UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm)) (certificate I.ctag I.constructorTag formula leftTerm rightTerm)))) := by
 obtain ⟨hc⟩ := internalCore p old arithmetic x I formula leftTerm rightTerm index fuel
 obtain ⟨hi⟩ := SixSol20261113.FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.verifierTag I.coreTag (UniformClosedRule12Certificate.checker old arithmetic x) I.h_verifier I.h_core
  index fuel .zero (.add (UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm)
   (UniformClosedRule12.conclusionValue I.caseTag I.predTag I.ctag formula leftTerm rightTerm)) (UniformClosedRule12Certificate.certificate I.ctag I.constructorTag formula leftTerm rightTerm)
 let T := GorbowPRNumeralCalculation.Theory p
 let H := UniformClosedRule12.guards I.fval I.vtag formula leftTerm rightTerm
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hcore := Hilbert.Local.mp (.base hc) hh
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hi) hcore))⟩
/-- The three actual machine conclusions share the same guards, code and fuel. -/
theorem exactCertificate : Targets.InternalCertificate := by
 intro n p old arithmetic x I ctx formula leftTerm rightTerm index fuel
 obtain ⟨hrun⟩ := RunProof.internalSingletonRun p old arithmetic x I formula leftTerm rightTerm index fuel
 obtain ⟨hcore⟩ := internalCore p old arithmetic x I formula leftTerm rightTerm index fuel
 obtain ⟨hfuel⟩ := internalFuel p old arithmetic x I formula leftTerm rightTerm index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let A := UniformClosedRule12.guards I.fval I.vtag formula leftTerm rightTerm
 have hh : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hr := Hilbert.Local.mp (.base hrun) hh
 have hc := Hilbert.Local.mp (.base hcore) hh
 have hf := Hilbert.Local.mp (.base hfuel) hh
 have hcf := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hc) hf
 have hout := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hr) hcf
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.CoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.CoreProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.CoreProof.internalCore
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate.CoreProof.internalFuel
