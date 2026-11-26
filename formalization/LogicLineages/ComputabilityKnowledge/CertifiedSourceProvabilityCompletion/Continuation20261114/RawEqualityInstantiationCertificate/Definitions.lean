module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113
abbrev kernel (a b : Term 1) (old arithmetic : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator (RawEqualityInstantiationAcceptance.logicalLeaf a b old) arithmetic x
abbrev checker (a b : Term 1) (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker LiteralSyntaxValidator.lineValidator (RawEqualityInstantiationAcceptance.logicalLeaf a b old) arithmetic x
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev verifier (a b : Term 1) (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (checker a b old arithmetic x)
/-- Finite literal AST interface; no runtime success is assumed. -/
structure Installation {n : Nat} (p : Program n) (a b : Term 1) (old arithmetic : Program 1) (x : Program 3) extends
 RawEqualityInstantiationDispatcher.Installation p a b old arithmetic x where
 itag : Nat
 qctag : Nat
 utag : Nat
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel a b old arithmetic x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,checker a b old arithmetic x⟩
 hu : (nodes p)[utag]? = some ⟨5,verifier a b old arithmetic x⟩
def certificate {ctx : Nat} (ctag qtag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (call qtag (raw ::ᵥ nil)) .zero
def output {ctx : Nat} (a b : Term 1) (ptag ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (RawEqualityInstantiation.formulaValue ctag atag a b raw) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationCertificate
