module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationCertificates.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Actual rule1 line, with arbitrary original payload/annotation and exactly zero references. -/
def line {ctx : Nat} (ptag : Nat) (formula payload args : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag formula
  (HistoryKernel.pairCall ptag (.succ .zero)
   (HistoryKernel.pairCall ptag payload (HistoryKernel.pairCall ptag args (HistoryKernel.pairCall ptag .zero .zero)))))
abbrev leafCall {ctx : Nat} (tag : Nat) (line : Term ctx) : Term ctx :=
 TwoSol20261113.ReflexivityRecognizer.leafCall tag line
def certificate {ctx : Nat} (ptag ctag : Nat) (formula payload args : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (line ptag formula payload args) .zero
structure Installation {n : Nat} (p : Program n) (logical old : Program 1) (x : Program 3) where
 ptag : Nat
 ctag : Nat
 ftag : Nat
 ltag : Nat
 oldTag : Nat
 newTag : Nat
 dtag : Nat
 itag : Nat
 qctag : Nat
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 hl : (nodes p)[ltag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩
 ho : (nodes p)[oldTag]? = some ⟨1,old⟩
 hn : (nodes p)[newTag]? = some ⟨1,RawMultiplication.arithmeticLeaf old⟩
 hd : (nodes p)[dtag]? = some ⟨4,RawMultiplicationCertificates.ZeroDispatcher.dispatcher logical old x⟩
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (RawMultiplicationCertificates.ZeroCertificate.kernel logical old x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,RawMultiplicationCertificates.ZeroCertificate.checker logical old x⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention
