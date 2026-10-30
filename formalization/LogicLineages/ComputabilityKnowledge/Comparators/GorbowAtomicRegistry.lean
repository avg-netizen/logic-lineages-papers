module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistry

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicRegistry
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowRegistryTuple
open GorbowRegistryDispatch
open LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistry

def TupleExact : Prop := ∀ n code packed out,
  tupleSubstitute n code packed=some out ↔ ∃ codes : List Nat,
    packed=tuple codes ∧ GorbowSortedSimultaneousCode.substituteNumber n code codes=some out

def NewDispatch : Prop := ∀ a b c,
  functionProgram (header 1 1 [a])=(GorbowArithmeticEvaluation.sortedValue a).getD 0 ∧
  functionProgram (header 3 1 [a,b,c])=(tupleSubstitute a b c).getD 0

def OriginalDispatch : Prop := RelationLaws ground ∧ FunctionLaws ground

def ActualCalibration : Prop :=
  (∀ (t : Term 0), ArithmeticTerm t → ∀ I,
    functionProgram (header 1 1 [termCode t])=t.realize I Fin.elim0) ∧
  (∀ n (φ : Formula n) (σ : Fin n → Term 0),
    functionProgram (header 3 1 [n,formulaCode φ,tuple (List.ofFn (fun i => termCode (σ i)))])=
      formulaCode (GorbowFormulaSubstitution.substituteFormula σ φ))

def Fallback : Prop :=
  (∀ code, GorbowRegistryDecoder.decodeHeader code=none → functionProgram code=GorbowSortedRegistry.functionProgram code) ∧
  (∀ arity tag args, ¬(arity=1 ∧ tag=1 ∧ args.length=1) →
    ¬(arity=3 ∧ tag=1 ∧ args.length=3) →
    functionProgram (header arity tag args)=GorbowSortedRegistry.functionProgram (header arity tag args))

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat × Nat => tupleSubstitute p.1 p.2.1 p.2.2) ∧ Primrec functionProgram

def Target : Prop := TupleExact ∧ NewDispatch ∧ OriginalDispatch ∧ ActualCalibration ∧ Fallback ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicRegistry
