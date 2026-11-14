module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalRetention.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalRetention.LeafProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem internalRetention : Targets.InternalRetention := by
 intro n p old oldTag newTag ho hn ctx line
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (RawLogicalRetention.leafCall oldTag line) (.succ .zero)
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hold : Computes p G old (line ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag oldTag 1 old ht ho ctx (line ::ᵥ nil)
  exact ⟨localTrans _ _ _ (.base hcopy) hh⟩
 obtain ⟨hout⟩ := RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G
  RawUniversalReplace.recognizer old (HistoryRuleSuffix.constant 1 1) (line ::ᵥ nil) (.succ .zero)
  hold (constantValue p G (line ::ᵥ nil) 1) newTag hn
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalRetention.LeafProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalRetention.LeafProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalRetention.LeafProof.internalRetention
