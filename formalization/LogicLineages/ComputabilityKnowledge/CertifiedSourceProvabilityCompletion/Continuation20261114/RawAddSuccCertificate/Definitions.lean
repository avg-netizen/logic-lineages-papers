module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccDispatcher.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
abbrev kernel (logical old : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator logical (RawAddSucc.arithmeticLeaf old) x
abbrev checker (logical old : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker LiteralSyntaxValidator.lineValidator logical (RawAddSucc.arithmeticLeaf old) x
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev verifier (logical old : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (checker logical old x)
/-- Finite literal AST interface; no runtime success is assumed. -/
structure Installation {n : Nat} (p : Program n) (logical old : Program 1) (x : Program 3) extends
 RawAddSuccDispatcher.Installation p logical old x where
 itag : Nat
 qctag : Nat
 utag : Nat
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel logical old x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,checker logical old x⟩
 hu : (nodes p)[utag]? = some ⟨5,verifier logical old x⟩
def certificate {ctx : Nat} (ctag qtag : Nat) (raw rawB : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (RawAddSucc.lineCall qtag raw rawB) .zero
def output {ctx : Nat} (ptag ctag atag : Nat) (raw rawB : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (RawAddSucc.equalityValue ctag atag raw rawB) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSuccCertificate
