module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
/-- Original token7 implication with fixed token10 quantified unary equality
antecedent; arbitrary symbolic closed substitution in the consequent. -/
def InternalFormulaValidity : Prop := ∀ (a b : Term 1) n (p : Program n)
 (vtag ftag ptag ctag atag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid vtag raw)
  (.equal (LiteralSyntaxValidator.formulaCall ftag .zero
   (RawEqualityInstantiation.formulaValue ctag atag a b raw)) (.succ .zero))))
/-- Original rule0/tag13 [phi,u], arbitrary index/fuel/history including zero.
Logical and grammar success are derived, not assumed. -/
def InternalDispatcher : Prop := ∀ (a b : Term 1) n (p : Program n)
 (old arithmetic : Program 1) (x : Program 3) (I : Installation p a b old arithmetic x),
 ∀ ctx (raw index fuel history : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.vtag raw)
  (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history
   (call I.qtag (raw ::ᵥ nil))) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.Targets
