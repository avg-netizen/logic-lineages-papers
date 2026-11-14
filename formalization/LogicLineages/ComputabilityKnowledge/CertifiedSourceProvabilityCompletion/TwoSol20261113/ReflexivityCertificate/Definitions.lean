module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.CoreProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ValidatorStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector
open SixSol20261113
abbrev validity : Program 1 := LiteralSyntaxValidator.lineValidator
abbrev logical (old : Program 1) : Program 1 := ReflexivityRecognizer.logicalLeaf old
abbrev dispatcher (old arithmetic : Program 1) (axiomProgram : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher validity (logical old) arithmetic axiomProgram
abbrev kernel (old arithmetic : Program 1) (axiomProgram : Program 3) : Program 3 :=
 HistoryKernel.kernel validity (logical old) arithmetic axiomProgram
abbrev checker (old arithmetic : Program 1) (axiomProgram : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker validity (logical old) arithmetic axiomProgram
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
/-- All fields below witness exact AST installation only; no acceptance premise. -/
structure Installation {k n : Nat} (p : Program n) (t : Term k)
 (old arithmetic : Program 1) (axiomProgram : Program 3) where
 qtag : Nat
 etag : Nat
 ttag : Nat
 ptag : Nat
 ctag : Nat
 atag : Nat
 vtag : Nat
 ftag : Nat
 ltag : Nat
 btag : Nat
 dtag : Nat
 itag : Nat
 qctag : Nat
 hq : (nodes p)[qtag]? = some ⟨k,LiteralReflexivityQuote.lineQuote t⟩
 he : (nodes p)[etag]? = some ⟨k,LiteralEqualityQuote.equalityQuote t t⟩
 ht : (nodes p)[ttag]? = some ⟨k,LiteralTemplateQuote.templateQuote t⟩
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
 hv : (nodes p)[vtag]? = some ⟨1,ReflexivityRecognizer.termValidator⟩
 hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 hl : (nodes p)[ltag]? = some ⟨1,validity⟩
 hb : (nodes p)[btag]? = some ⟨1,logical old⟩
 hd : (nodes p)[dtag]? = some ⟨4,dispatcher old arithmetic axiomProgram⟩
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel old arithmetic axiomProgram)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,checker old arithmetic axiomProgram⟩
def line {k ctx : Nat} (qtag : Nat) (values : List.Vector (Term ctx) k) : Term ctx :=
 LiteralReflexivityQuote.quoteCall qtag values
def raw {k ctx : Nat} (etag : Nat) (values : List.Vector (Term ctx) k) : Term ctx :=
 LiteralEqualityQuote.quoteCall etag values
/-- The genuine original singleton list of full proof lines. -/
def certificate {k ctx : Nat} (ctag qtag : Nat) (values : List.Vector (Term ctx) k) : Term ctx :=
 HistoryLookup.consCall ctag (line qtag values) .zero
def output {k ctx : Nat} (ptag ctag etag : Nat) (values : List.Vector (Term ctx) k) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero (raw etag values) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate
