module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmeticDefinitions

@[expose] public section
/-! A literal structural compiler for arithmetic templates in the EXISTING
Term syntax. Universal-function nodes are rejected by `arithmetic`; their
total fallback compilation has no correctness claim. Actual substitution
arguments may still contain every source-language function. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler
open GorbowSyntax GorbowPRProgram

def arithmetic {n : Nat} : Term n → Prop
  | .var _ => True
  | .zero => True
  | .succ t => arithmetic t
  | .add t u => arithmetic t ∧ arithmetic u
  | .mul t u => arithmetic t ∧ arithmetic u
  | .universalFunction _ => False

def zeroProgram (n : Nat) : Program n := .composition .zero Fin.elim0

def compile {n : Nat} : Term n → Program n
  | .var i => .projection i
  | .zero => zeroProgram n
  | .succ t => .composition .succ (fun _ : Fin 1 => compile t)
  | .add t u => .composition GorbowPRInternalArithmetic.addition
      (Fin.cases (compile u) (fun _ : Fin 1 => compile t))
  | .mul t u => .composition GorbowPRInternalArithmetic.multiplication
      (Fin.cases (compile u) (fun _ : Fin 1 => compile t))
  | .universalFunction _ => zeroProgram n

/-- The arithmetic multiplexing header already used by the actual source. -/
def headerTemplate (arity tag : Nat) : Term arity :=
  GorbowRegistryTuple.headerTerm arity tag
    (GorbowPRDefiningEquations.argumentVariables arity).toList

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler
