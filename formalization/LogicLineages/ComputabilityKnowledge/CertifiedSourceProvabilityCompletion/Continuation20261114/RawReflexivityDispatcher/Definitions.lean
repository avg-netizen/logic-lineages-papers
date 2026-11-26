module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Literal finite AST interface, independent of any term template. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) where
 qtag : Nat
 ptag : Nat
 ctag : Nat
 atag : Nat
 vtag : Nat
 ftag : Nat
 ltag : Nat
 btag : Nat
 dtag : Nat
 hq : (nodes p)[qtag]? = some ⟨1,RawReflexivity.lineConstructor⟩
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
 hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩
 hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 hl : (nodes p)[ltag]? = some ⟨1,TwoSol20261113.ReflexivityCertificate.validity⟩
 hb : (nodes p)[btag]? = some ⟨1,TwoSol20261113.ReflexivityCertificate.logical old⟩
 hd : (nodes p)[dtag]? = some ⟨4,TwoSol20261113.ReflexivityCertificate.dispatcher old a x⟩
def valid {ctx : Nat} (vtag : Nat) (raw : Term ctx) : Formula ctx :=
 .equal (TwoSol20261113.ReflexivityRecognizer.leafCall vtag raw) (.succ .zero)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivityDispatcher
