module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.DecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.GuardProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open OriginalQuantifierLogicalProducers
open SixSol20261112.Fuel NamedArithmeticGraph
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem guardAt {n inputs ctx : Nat} (p : Program n) (G : List (Formula ctx)) (arity fval : Nat)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (q : Program inputs) (av : List.Vector (Term ctx) inputs) (a : Term ctx)
 (hq : Computes p G q av a) (hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid arity fval a)) :
 Computes p G (formulaGuard arity q) av (.succ .zero) := by
 have hv : Computes p G LiteralSyntaxValidator.formulaValidator ((Term.numeral arity : Term ctx) ::ᵥ a ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag fval 2
   LiteralSyntaxValidator.formulaValidator ht hf ctx ((Term.numeral arity : Term ctx) ::ᵥ a ::ᵥ nil)
  exact ⟨HistoryCodec.ArithmeticSupport.localTrans _ _ _ (.base hcopy) hvalid⟩
 exact binary p G av LiteralSyntaxValidator.formulaValidator (constant inputs arity) q
  (Term.numeral arity) a (.succ .zero) (constantValue p G av arity) hq hv

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.GuardProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.GuardProof
