module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationDispatcher
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
abbrev dispatcher (f : Formula 1) (old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator
  (FullFormulaInstantiation.logicalLeaf f old) arithmetic x
structure Installation {n : Nat} (p : Program n) (f : Formula 1) (old arithmetic : Program 1) (x : Program 3) where
 qtag : Nat
 ptag : Nat
 ctag : Nat
 atag : Nat
 vtag : Nat
 ftag : Nat
 ltag : Nat
 btag : Nat
 dtag : Nat
 hq : (nodes p)[qtag]? = some ⟨1,FullFormulaInstantiation.line f⟩
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
 hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩
 hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 hl : (nodes p)[ltag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩
 hb : (nodes p)[btag]? = some ⟨1,FullFormulaInstantiation.logicalLeaf f old⟩
 hd : (nodes p)[dtag]? = some ⟨4,dispatcher f old arithmetic x⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationDispatcher
