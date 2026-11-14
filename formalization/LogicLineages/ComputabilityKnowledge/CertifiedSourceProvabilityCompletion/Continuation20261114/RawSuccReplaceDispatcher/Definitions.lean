module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceDispatcher
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Actual original dispatcher with refined logical equality-replacement leaf
and unchanged arbitrary arithmetic and axiom leaves. -/
abbrev dispatcher (old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator (RawSuccReplace.logicalLeaf old) arithmetic x
structure Installation {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3) where
 qtag : Nat
 ptag : Nat
 ctag : Nat
 atag : Nat
 vtag : Nat
 ftag : Nat
 ltag : Nat
 btag : Nat
 dtag : Nat
 hq : (nodes p)[qtag]? = some ⟨2,RawSuccReplace.lineConstructor⟩
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
 hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩
 hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 hl : (nodes p)[ltag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩
 hb : (nodes p)[btag]? = some ⟨1,RawSuccReplace.logicalLeaf old⟩
 hd : (nodes p)[dtag]? = some ⟨4,dispatcher old arithmetic x⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceDispatcher
