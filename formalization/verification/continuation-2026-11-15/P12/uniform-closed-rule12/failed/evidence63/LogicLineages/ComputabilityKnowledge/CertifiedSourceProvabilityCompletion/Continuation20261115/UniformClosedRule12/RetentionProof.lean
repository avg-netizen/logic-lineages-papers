module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.RetentionProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem exactInternalRetainsCase13 : Targets.InternalRetainsCase13 := by
 intro n p old oldTag newTag ho hn ctx line
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (RawLogicalRetention.leafCall oldTag line) (.succ .zero)
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hold : Computes p G (UniformClosedRule13.logicalLeaf old) (line ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag oldTag 1 (UniformClosedRule13.logicalLeaf old) ht ho ctx (line ::ᵥ nil)
  exact ⟨localTrans _ _ _ (.base hcopy) hh⟩
 obtain ⟨hout⟩ := RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G
  recognizer (UniformClosedRule13.logicalLeaf old) (HistoryRuleSuffix.constant 1 1) (line ::ᵥ nil) (.succ .zero)
  hold (constantValue p G (line ::ᵥ nil) 1) newTag hn
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.RetentionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.RetentionProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.RetentionProof.exactInternalRetainsCase13
