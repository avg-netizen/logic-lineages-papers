module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.DecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.GuardProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem guardAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (fval : Nat)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (q : Program arity) (av : List.Vector (Term ctx) arity) (a : Term ctx)
 (hq : Computes p G q av a) (hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid fval a)) :
 Computes p G (formulaGuard q) av (.succ .zero) := by
 have hv : Computes p G LiteralSyntaxValidator.formulaValidator ((.zero : Term ctx) ::ᵥ a ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag fval 2
   LiteralSyntaxValidator.formulaValidator ht hf ctx (.zero ::ᵥ a ::ᵥ nil)
  exact ⟨localTrans _ _ _ (.base hcopy) hvalid⟩
 exact binary p G av LiteralSyntaxValidator.formulaValidator (constant arity 0) q
  .zero a (.succ .zero) (constantValue p G av 0) hq hv
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.GuardProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.GuardProof
