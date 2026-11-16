module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- Exact original line payload decoders, shared with existing schema recognizers. -/
def firstArg : Program 1 := TwoSol20261113.ReflexivityRecognizer.termCode
def secondArg : Program 1 := Continuation20261114.RawAddSucc.secondTermCode
def formulaGuard {n : Nat} (arity : Nat) (a : Program n) : Program n :=
 applyTwo LiteralSyntaxValidator.formulaValidator (constant n arity) a
/-- Equality with the whole original line enforces conclusion, context,
annotation, payload length and references, not merely a tag test. -/
def recognizer (isExists : Bool) : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (OriginalQuantifierLogicalProducers.line isExists firstArg secondArg))
 (if isExists then formulaGuard 1 firstArg
  else conjunction (formulaGuard 0 firstArg) (formulaGuard 0 secondArg))
/-- Concrete conservative candidate leaf: positive duality/contraposition hits
return1; every other numeric line follows the unchanged arbitrary old AST. -/
def logicalLeaf (old : Program 1) : Program 1 :=
 choose (recognizer true) (choose (recognizer false) old (constant 1 1)) (constant 1 1)
def formulaValid {ctx : Nat} (arity fval : Nat) (a : Term ctx) : Formula ctx :=
 .equal (LiteralSyntaxValidator.formulaCall fval (Term.numeral arity) a) (.succ .zero)
def guards {ctx : Nat} (isExists : Bool) (fval : Nat) (a b : Term ctx) : Formula ctx :=
 if isExists then formulaValid 1 fval a
 else .conj (formulaValid 0 fval a) (formulaValid 0 fval b)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension
