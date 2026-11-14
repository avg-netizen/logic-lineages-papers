module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.CoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalCore : Targets.InternalCore := by
 intro n p old arithmetic x I ctx raw rawB rawV index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.validatorTag raw
 let K := RawReflexivityDispatcher.valid I.validatorTag rawB
 let L := RawReflexivityDispatcher.valid I.validatorTag rawV
 let G := [L,K,H]
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hkValid : Hilbert.Local T ctx G K := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hlValid : Hilbert.Local T ctx G L := .hypothesis List.mem_cons_self
 let code := RawAddLeftCertificate.certificate I.consTag I.qtag raw rawB rawV
 let eq := RawAddLeftReplace.formulaValue I.consTag I.appendTag raw rawB rawV
 let it := I.qctag+LiteralCheckerAcceptance.iteratorOffset LiteralSyntaxValidator.lineValidator (RawAddLeftReplace.logicalLeaf old) arithmetic x
 let run := LiteralCheckerAcceptance.runCall it I.pairTag index fuel code
 obtain ⟨hrun⟩ := RunProof.internalSingletonRun n p old arithmetic x I ctx raw rawB rawV index fuel
 obtain ⟨hf,hi⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p I.qctag LiteralSyntaxValidator.lineValidator (RawAddLeftReplace.logicalLeaf old) arithmetic x I.hqc
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p it I.itag 4
  (SixSol20261112.HistoryMachine.iterator (RawAddLeftCertificate.kernel old arithmetic x)) hi I.hi ctx
  (code ::ᵥ HistoryRunSplice.state I.pairTag (.succ .zero) code ::ᵥ index ::ᵥ fuel ::ᵥ nil)
 have hstate := localTrans _ _ _ (.base hcopy) (.mp (.mp (.mp (.base hrun) hh) hkValid) hlValid)
 obtain ⟨hcomplete⟩ := LiteralCheckerAcceptance.CompletenessProof.completeBody p (I.qctag+1) I.pairTag I.consTag hf I.hp I.hc
  run .zero (.add eq eq) code eq .zero
 have hbody : Hilbert.Local T ctx G (LiteralCheckerAcceptance.WitnessProof.body I.pairTag I.consTag run .zero (.add eq eq) eq .zero) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (.base (.logical (.reflexive (.add eq eq))))) hstate
 have hfinish := Hilbert.Local.mp (.base hcomplete) hbody
 obtain ⟨hnorm⟩ := LiteralCheckerAcceptance.NormalizationProof.internalCoreNormalization n p I.qctag I.pairTag
  LiteralSyntaxValidator.lineValidator (RawAddLeftReplace.logicalLeaf old) arithmetic x I.hqc I.hp ctx index fuel .zero (.add eq eq) code
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (localTrans _ _ _ (.base hnorm) hfinish))))⟩

theorem internalFuel : Targets.InternalFuel := by
 intro n p old arithmetic x I ctx raw rawB rawV index fuel
 obtain ⟨hc⟩ := internalCore n p old arithmetic x I ctx raw rawB rawV index fuel
 obtain ⟨hi⟩ := SixSol20261113.FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.utag I.qctag (RawAddLeftCertificate.checker old arithmetic x) I.hu I.hqc
  index fuel .zero (.add (RawAddLeftReplace.formulaValue I.consTag I.appendTag raw rawB rawV)
   (RawAddLeftReplace.formulaValue I.consTag I.appendTag raw rawB rawV)) (RawAddLeftCertificate.certificate I.consTag I.qtag raw rawB rawV)
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.validatorTag raw
 let K := RawReflexivityDispatcher.valid I.validatorTag rawB
 let L := RawReflexivityDispatcher.valid I.validatorTag rawV
 let G := [L,K,H]
 have hh : Hilbert.Local T ctx G H := .hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have hkValid : Hilbert.Local T ctx G K := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hlValid : Hilbert.Local T ctx G L := .hypothesis List.mem_cons_self
 have hcore := Hilbert.Local.mp (Hilbert.Local.mp (Hilbert.Local.mp (.base hc) hh) hkValid) hlValid
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.base hi) hcore))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.CoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.CoreProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.CoreProof.internalCore
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftCertificate.CoreProof.internalFuel
