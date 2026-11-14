module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.CoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 TwoSol20261113.ReflexivityCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internalCore : Targets.InternalCore := by
 intro n p old arithmetic x I ctx raw index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid I.vtag raw
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 let code := RawCumulativeLogical.certificate I.ctag I.qtag raw
 let eq := RawReflexivity.equalityValue I.ctag I.atag raw
 let it := I.qctag+LiteralCheckerAcceptance.iteratorOffset validity (RawCumulativeLogical.logical old) arithmetic x
 let run := LiteralCheckerAcceptance.runCall it I.ptag index fuel code
 obtain ⟨hrun⟩ := RunProof.internalSingletonRun n p old arithmetic x I ctx raw index fuel
 obtain ⟨hf,hi⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p I.qctag validity (RawCumulativeLogical.logical old) arithmetic x I.hqc
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p it I.itag 4
  (SixSol20261112.HistoryMachine.iterator (RawCumulativeLogical.kernel old arithmetic x)) hi I.hi ctx
  (code ::ᵥ HistoryRunSplice.state I.ptag (.succ .zero) code ::ᵥ index ::ᵥ fuel ::ᵥ nil)
 have hstate := localTrans _ _ _ (.base hcopy) (.mp (.base hrun) hh)
 obtain ⟨hcomplete⟩ := LiteralCheckerAcceptance.CompletenessProof.completeBody p (I.qctag+1) I.ptag I.ctag hf I.hp I.hc
  run .zero (.add eq eq) code eq .zero
 have hbody : Hilbert.Local T ctx G (LiteralCheckerAcceptance.WitnessProof.body I.ptag I.ctag run .zero (.add eq eq) eq .zero) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) (.base (.logical (.reflexive (.add eq eq))))) hstate
 have hfinish := Hilbert.Local.mp (.base hcomplete) hbody
 obtain ⟨hnorm⟩ := LiteralCheckerAcceptance.NormalizationProof.internalCoreNormalization n p I.qctag I.ptag
  validity (RawCumulativeLogical.logical old) arithmetic x I.hqc I.hp ctx index fuel .zero (.add eq eq) code
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hnorm) hfinish))⟩

theorem internalFuel : Targets.InternalFuel := by
 intro n p old a x I ctx raw index fuel
 obtain ⟨hc⟩ := internalCore n p old a x I ctx raw index fuel
 obtain ⟨hi⟩ := SixSol20261113.FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.utag I.qctag (RawCumulativeLogical.checker old a x) I.hu I.hqc
  index fuel .zero (.add (RawReflexivity.equalityValue I.ctag I.atag raw)
   (RawReflexivity.equalityValue I.ctag I.atag raw)) (RawCumulativeLogical.certificate I.ctag I.qtag raw)
 exact ⟨Hilbert.compose hi hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.CoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.CoreProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.CoreProof.internalCore
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.CoreProof.internalFuel
