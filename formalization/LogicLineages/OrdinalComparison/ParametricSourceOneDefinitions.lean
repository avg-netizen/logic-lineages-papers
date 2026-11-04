module
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceOne
open SourceAdditionCompletion

def identityVector (Γ : List Ty) : OrdinalVector Γ 0 := fun _ =>
  .collapse .one (.add (.add (.add .one .one) .one) .one)
def OneWitness (G : Nat → Nat) (u v d : Nat) : Prop :=
  ParametricSourceAddition.Equation G (extend (singletonVal u) v)
    (successorProbe .here) (.app identity .zeroC) ∧
  ParametricSourceAddition.AddWitness G (extend (singletonVal u) v)
    (.there .here) (.there .here) .here d
def OneFormula (G : Nat → Nat) (u : Nat) : Prop := ∃ v : Nat,
  ParametricSourceAddition.Equation G (extend (singletonVal u) v)
    (successorProbe .here) (.app identity .zeroC) ∧
  ParametricSourceAddition.AddFormula G (extend (singletonVal u) v)
    (.there .here) (.there .here) .here
end LogicLineages.OrdinalComparison.Source.ParametricSourceOne
