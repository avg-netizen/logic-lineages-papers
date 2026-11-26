module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ReplacementCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityRecognizer
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem internalUniversalValidity : ∀ n (p : Program n) (vtag ptag ctag : Nat),
 (nodes p)[vtag]? = some ⟨1,termValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid vtag raw) (RawReflexivityDispatcher.valid vtag (RawUniversalReplace.universalValue ctag raw)))) := by
 intro n p vtag ptag ctag hv hp hc ctx raw
 obtain ⟨stag,hs⟩ := TermInternalProof.scanInstalled p vtag hv
 obtain ⟨hsound⟩ := RawReflexivityDispatcher.TermSoundProof.sound p vtag stag ptag ctag hv hs hp hc raw
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hsucc⟩ := LiteralTemplateQuote.TermScanProof.scanUniversal p stag ptag ctag hs hp hc .zero .zero raw
 have hscan := localTrans _ _ _ (.base hsucc) (.mp (.base hsound) hh)
 obtain ⟨hvout⟩ := RawSuccCongruence.ValidityProof.localBinding p [H] vtag stag ptag ctag hv hs hp hc (RawUniversalReplace.universalValue ctag raw) hscan
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hvout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ValidityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ValidityProof.internalUniversalValidity
