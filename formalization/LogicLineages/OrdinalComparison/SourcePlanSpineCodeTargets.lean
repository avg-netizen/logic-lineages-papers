module
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.Targets
open ExistentialPlan

def ExactCompilation : Prop := ∀ {Γ} (q : Plan Γ), ParametricExistentialPlan.Supported q →
  (∀ i ∈ spine q, i.1 ≤ 4) ∧ run (spine q) = (q.witnesses,compiledPairs q)

def ExactAggregate : Prop := ∀ {Γ} (q : Plan Γ), ParametricExistentialPlan.Supported q →
  let es := (compile q).forest.map (fun p => (p.1.term,p.2.term))
  let a := SourceAggregateCompletion.aggregate es
  aggregateCode (spine q) = (SyntaxCode.encodeTerm a.1,SyntaxCode.encodeTerm a.2)

def UniformPrimitiveRecursive : Prop :=
  Primrec (fun p : Instruction × State => step p.1 p.2) ∧ Primrec run ∧ Primrec aggregateCode
end LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.Targets
