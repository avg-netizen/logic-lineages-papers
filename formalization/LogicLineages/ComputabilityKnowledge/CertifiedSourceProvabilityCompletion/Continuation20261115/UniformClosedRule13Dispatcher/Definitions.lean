module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationDispatcher.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Dispatcher
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Original dispatcher with the exact new uniform logical leaf. No other
rule branch or validator AST is changed. -/
abbrev dispatcher (old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator
  (UniformClosedRule13.logicalLeaf old) arithmetic x
/-- Only actual same-root memberships. Prior validity installation is preserved;
no line, logical-leaf, scanner or dispatcher success is assumed. -/
structure Installation {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 extends UniformClosedRule13Validity.Installation p where
 constructorTag : Nat
 lineTag : Nat
 logicalTag : Nat
 dispatcherTag : Nat
 h_constructor : (nodes p)[constructorTag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩
 h_line : (nodes p)[lineTag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩
 h_logical : (nodes p)[logicalTag]? = some ⟨1,UniformClosedRule13.logicalLeaf old⟩
 h_dispatcher : (nodes p)[dispatcherTag]? = some ⟨4,dispatcher old arithmetic x⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Dispatcher
