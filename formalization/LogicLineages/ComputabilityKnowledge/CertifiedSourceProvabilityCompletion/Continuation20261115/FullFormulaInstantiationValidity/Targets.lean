module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Targets
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
/-- Original token7 implication with fixed token10 quantified FULL unary formula
antecedent, including arbitrary nested binders; arbitrary symbolic closed substitution
in the consequent. Actual original grammar acceptance must be DERIVED internally. -/
def InternalFormulaValidity : Prop := ∀ (f : Formula 1) n (p : Program n)
 (vtag ftag ptag ctag atag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid vtag raw)
  (.equal (LiteralSyntaxValidator.formulaCall ftag .zero
   (formulaValue ctag atag f raw)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Targets
