module

public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatch

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalRegistry
open GorbowSyntax GorbowRegistryTuple GorbowRegistryDecoder GorbowSortedSyntaxCode
open LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistry

def NewDispatch : Prop := ∀ code, functionProgram (header 1 2 [code])=
  (GorbowSortedSelfApplication.selfApply code).getD 0

def OriginalDispatch : Prop := GorbowRegistryDispatch.RelationLaws ground ∧ GorbowRegistryDispatch.FunctionLaws ground

def AtomicDispatch : Prop := ∀ a b c,
  functionProgram (header 1 1 [a])=(GorbowArithmeticEvaluation.sortedValue a).getD 0 ∧
  functionProgram (header 3 1 [a,b,c])=(GorbowAtomicRegistry.tupleSubstitute a b c).getD 0

def ActualCalibration : Prop := ∀ φ : Formula 1,
  functionProgram (header 1 2 [formulaCode φ])=formulaCode (GorbowSortedSelfApplication.selfInstance φ)

def Fallback : Prop :=
  (∀ code, decodeHeader code=none → functionProgram code=GorbowAtomicRegistry.functionProgram code) ∧
  (∀ arity tag args, ¬(arity=1 ∧ tag=2 ∧ args.length=1) →
    functionProgram (header arity tag args)=GorbowAtomicRegistry.functionProgram (header arity tag args))

def UniformProgram : Prop := Primrec functionProgram

def Target : Prop := NewDispatch ∧ OriginalDispatch ∧ AtomicDispatch ∧ ActualCalibration ∧ Fallback ∧ UniformProgram
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalRegistry
