module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationDispatcher.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113
abbrev kernel (f : Formula 1) (old arithmetic : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator (FullFormulaInstantiation.logicalLeaf f old) arithmetic x
abbrev checker (f : Formula 1) (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker LiteralSyntaxValidator.lineValidator (FullFormulaInstantiation.logicalLeaf f old) arithmetic x
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev verifier (f : Formula 1) (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (checker f old arithmetic x)
/-- Finite literal AST interface; no runtime success is assumed. -/
structure Installation {n : Nat} (p : Program n) (f : Formula 1) (old arithmetic : Program 1) (x : Program 3) extends
 FullFormulaInstantiationDispatcher.Installation p f old arithmetic x where
 itag : Nat
 qctag : Nat
 utag : Nat
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel f old arithmetic x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,checker f old arithmetic x⟩
 hu : (nodes p)[utag]? = some ⟨5,verifier f old arithmetic x⟩
def certificate {ctx : Nat} (ctag qtag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (call qtag (raw ::ᵥ nil)) .zero
def output {ctx : Nat} (f : Formula 1) (ptag ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (FullFormulaInstantiation.formulaValue ctag atag f raw) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate
