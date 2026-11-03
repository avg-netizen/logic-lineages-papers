module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntimeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BaseFormula
open CommonLayerSyntax

/-- Literal Boolean formulas in the source BASE signature0,1,+,<,actualPhi.
Numerals abbreviate finite additions of1. There is NO collapse/head/observer
predicate, variable-value supplier or extra function symbol. -/
inductive Formula where
  | truth | falsity
  | equal (left right:BaseTerm) | less (left right:BaseTerm)
  | negative (body:Formula) | conjunction (left right:Formula) | disjunction (left right:Formula)

def Formula.eval (ν:Nat→Nat):Formula→Prop
  | .truth=>True | .falsity=>False
  | .equal E F=>E.value ν=F.value ν | .less E F=>E.value ν<F.value ν
  | .negative p=>¬p.eval ν
  | .conjunction p q=>p.eval ν∧q.eval ν | .disjunction p q=>p.eval ν∨q.eval ν

def Formula.variables:Formula→List Nat
  | .truth | .falsity=>[]
  | .equal E F | .less E F=>E.variables++F.variables
  | .negative p=>p.variables
  | .conjunction p q | .disjunction p q=>p.variables++q.variables

/-- Atomic operand indices in this intermediate view are ACTUAL term codes,
which will be interpreted under their ONE original raw valuation. -/
def Formula.guardView:Formula→CommonHeadLargeGuards.Formula
  | .truth=>.truth | .falsity=>.falsity
  | .equal E F=>.eq E.encode F.encode | .less E F=>.lt E.encode F.encode
  | .negative p=>.neg p.guardView
  | .conjunction p q=>.conj p.guardView q.guardView
  | .disjunction p q=>.disj p.guardView q.guardView

def Formula.encode (p:Formula):List CommonHeadCompiler.Instruction:=CommonHeadCompiler.encode p.guardView

def termValuation (ν:Nat→Nat) (code:Nat):Nat:=(BaseTerm.decode code).value ν

def evaluate (ν:Nat→Nat) (code:List CommonHeadCompiler.Instruction):Bool:=
  GuardCodeRuntime.evaluate (termValuation ν) code

def rawVariables (code:List CommonHeadCompiler.Instruction):List Nat:=
  (GuardCodeRuntime.codeVariables code).flatMap (fun t=>(BaseTerm.decode t).variables)
end LogicLineages.OrdinalComparison.LayeredComparison.BaseFormula
