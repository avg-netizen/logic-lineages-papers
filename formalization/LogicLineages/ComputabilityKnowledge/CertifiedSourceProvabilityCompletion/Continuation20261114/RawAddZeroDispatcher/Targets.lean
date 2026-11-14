module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Independently internal grammar closure for original equality(add(t,zero),t).
The arithmetic truth of the equation is not reflected into syntactic validity. -/
def InternalFormulaValidity : Prop := ∀ n (p : Program n)
 (vtag ftag ptag ctag atag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.equal (LiteralSyntaxValidator.formulaCall ftag .zero
    (RawAddZero.equalityValue ctag atag raw)) (.succ .zero))))
/-- Actual original dispatcher: rule1 is selected only AFTER the failed rule0
test. All runtime index/fuel/history/raw values remain arbitrary. Only genuine
internal term-validity is an antecedent; no successful rule/dispatcher premise. -/
def InternalDispatcher : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x), ∀ ctx (raw index fuel history : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history
    (RawAddZero.lineCall I.qtag raw)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher.Targets
