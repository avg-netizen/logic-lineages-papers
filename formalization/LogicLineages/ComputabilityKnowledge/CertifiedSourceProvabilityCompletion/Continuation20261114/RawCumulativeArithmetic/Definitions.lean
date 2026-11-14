module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Select both original arithmetic schemas before any source witnesses.
The original all-input fallback remains old; no source is changed in place. -/
def arithmetic (old : Program 1) : Program 1 :=
 RawAddSucc.arithmeticLeaf (RawAddZero.arithmeticLeaf old)
abbrev dispatcher (logical old : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator logical (arithmetic old) x
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
 hb : (nodes p)[btag]? = some ⟨1,arithmetic old⟩
 hd : (nodes p)[dtag]? = some ⟨4,dispatcher logical old x⟩
abbrev kernel (logical old : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator logical (arithmetic old) x
abbrev checker (logical old : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker LiteralSyntaxValidator.lineValidator logical (arithmetic old) x
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev verifier (logical old : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (checker logical old x)
/-- Finite literal AST interface; no runtime success is assumed. -/
structure CertificateInstallation {n : Nat} (p : Program n) (logical old : Program 1) (x : Program 3) extends
 Installation p logical old x where
 itag : Nat
 qctag : Nat
 utag : Nat
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel logical old x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,checker logical old x⟩
 hu : (nodes p)[utag]? = some ⟨5,verifier logical old x⟩
def certificate {ctx : Nat} (ctag qtag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (RawAddZero.lineCall qtag raw) .zero
def output {ctx : Nat} (ptag ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (RawAddZero.equalityValue ctag atag raw) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic
