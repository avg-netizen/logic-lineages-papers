module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Dispatcher.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev kernel (old arithmetic : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x
abbrev checker (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker LiteralSyntaxValidator.lineValidator (UniformClosedRule12.logicalLeaf old) arithmetic x
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev verifier (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (checker old arithmetic x)
/-- Actual same-root memberships only. iteratorTag differs from inherited itag,
which denotes the instance recognizer, and from the substitution fold ftag. -/
structure Installation {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 extends toDispatcherInstallation : UniformClosedRule12Dispatcher.Installation p old arithmetic x where
 iteratorTag : Nat
 coreTag : Nat
 verifierTag : Nat
 h_iterator : (nodes p)[iteratorTag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel old arithmetic x)⟩
 h_core : (nodes p)[coreTag]? = some ⟨5,checker old arithmetic x⟩
 h_verifier : (nodes p)[verifierTag]? = some ⟨5,verifier old arithmetic x⟩
def certificate {ctx : Nat} (ctag constructorTag : Nat) (formula leftTerm rightTerm : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (UniformClosedRule12.lineCall constructorTag formula leftTerm rightTerm) .zero
def output {ctx : Nat} (ptag ctag caseTag predTag : Nat) (formula leftTerm rightTerm : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (UniformClosedRule12.conclusionValue caseTag predTag ctag formula leftTerm rightTerm) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Certificate
