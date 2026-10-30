module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticAxiomCode
open GorbowSyntax GorbowPACore
open GorbowLogicalAxiomCode (Annotation)
open LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCode

def ExactCompilation : Prop := ∀ n annotation out, compile n annotation = some out ↔
  ∃ w : ArithmeticInstance n, annotation = encode w ∧ out = GorbowFormulaPrefixCode.encode (arithmeticFormula w)

def AnnotationInjection : Prop := ∀ n : Nat, Function.Injective (@encode n)

def UniformProgram : Prop := Primrec (fun p : Nat × Annotation => compile p.1 p.2)

def Target : Prop := ExactCompilation ∧ AnnotationInjection ∧ UniformProgram
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticAxiomCode
