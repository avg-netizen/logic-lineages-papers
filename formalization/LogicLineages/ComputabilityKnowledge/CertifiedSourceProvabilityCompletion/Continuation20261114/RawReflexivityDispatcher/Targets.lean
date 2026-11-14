module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual term-validator success gives actual equality-formula validity at
context zero. Both use the original prefix grammar, not reflected native truth. -/
def InternalEqualityValidity : Prop := ∀ n (p : Program n)
 (vtag ftag ptag ctag atag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (valid vtag raw)
   (.equal (LiteralSyntaxValidator.formulaCall ftag .zero
    (RawReflexivity.equalityValue ctag atag raw)) (.succ .zero))))
/-- Uniform actual original dispatcher acceptance at arbitrary index/fuel/history,
from the genuine INTERNAL term-validity antecedent, using one Program1 line
constructor. No successful validity/dispatcher premise, external template or
new checker semantics. This is not CORE/Fuel/source/HB3 completion. -/
def InternalDispatcher : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (raw index fuel history : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (valid I.vtag raw)
   (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history
    (RawReflexivity.lineCall I.qtag raw)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher.Targets
