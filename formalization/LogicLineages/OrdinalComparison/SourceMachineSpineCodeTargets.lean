module
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.Targets
open ExistentialPlan

def ExactSpine : Prop := ∀ b e,
  code b e=SourcePlanSpineCode.spine (SourceMachineConjunctionPlan.plan b e) ∧
  ParametricExistentialPlan.Supported (SourceMachineConjunctionPlan.plan b e)

def ExactOutputs : Prop := ∀ b e,
  let q := SourceMachineConjunctionPlan.plan b e
  let es := (compile q).forest.map (fun p => (p.1.term,p.2.term))
  let a := SourceAggregateCompletion.aggregate es
  compiled b e=(q.witnesses,SourcePlanSpineCode.compiledPairs q) ∧
  aggregate b e=(SyntaxCode.encodeTerm a.1,SyntaxCode.encodeTerm a.2)

def UniformPrimitiveRecursive : Prop :=
  Primrec₂ constant ∧ Primrec tail ∧ Primrec₂ code ∧ Primrec₂ compiled ∧ Primrec₂ aggregate
end LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.Targets
