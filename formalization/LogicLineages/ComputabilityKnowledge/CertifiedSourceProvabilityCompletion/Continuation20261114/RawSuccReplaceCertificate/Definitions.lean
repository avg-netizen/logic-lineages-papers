module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceDispatcher.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
abbrev kernel (old arithmetic : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator (RawSuccReplace.logicalLeaf old) arithmetic x
abbrev checker (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker LiteralSyntaxValidator.lineValidator (RawSuccReplace.logicalLeaf old) arithmetic x
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev verifier (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (checker old arithmetic x)
/-- Finite literal AST interface; no runtime success is assumed. -/
structure Installation {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3) extends
 RawSuccReplaceDispatcher.Installation p old arithmetic x where
 itag : Nat
 qctag : Nat
 utag : Nat
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel old arithmetic x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,checker old arithmetic x⟩
 hu : (nodes p)[utag]? = some ⟨5,verifier old arithmetic x⟩
def certificate {ctx : Nat} (ctag qtag : Nat) (raw rawB : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (RawSuccReplace.lineCall qtag raw rawB) .zero
def output {ctx : Nat} (ptag ctag atag : Nat) (raw rawB : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (RawSuccReplace.formulaValue ctag atag raw rawB) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplaceCertificate
