module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Actual original dispatcher, retaining its logical leaf unchanged while
using the calibrated explicit arithmetic add-zero leaf. -/
abbrev dispatcher (logical old : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator logical (RawAddZero.arithmeticLeaf old) x
structure Installation {n : Nat} (p : Program n) (logical old : Program 1) (x : Program 3) where
 qtag : Nat
 ptag : Nat
 ctag : Nat
 atag : Nat
 vtag : Nat
 ftag : Nat
 ltag : Nat
 btag : Nat
 dtag : Nat
 hq : (nodes p)[qtag]? = some ⟨1,RawAddZero.lineConstructor⟩
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
 hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩
 hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 hl : (nodes p)[ltag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩
 hb : (nodes p)[btag]? = some ⟨1,RawAddZero.arithmeticLeaf old⟩
 hd : (nodes p)[dtag]? = some ⟨4,dispatcher logical old x⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroDispatcher
