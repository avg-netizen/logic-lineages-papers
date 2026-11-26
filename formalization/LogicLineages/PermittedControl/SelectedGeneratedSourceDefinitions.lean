module
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceDefinitions
public import LogicLineages.PermittedControl.SelectedCanonicalDomainTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedGeneratedSource
open OrdinalComparison Source.ForwardTranslation

/-- The very same compiler tree, interpreted using the selected actual collapse. -/
noncomputable def scalarValueWith {ι : Type} (ctrl : Nat → Nat) (ρ : ι → Nat) : Scalar ι → Nat
  | .one => 1
  | .var x => ρ x
  | .add a b => scalarValueWith ctrl ρ a + scalarValueWith ctrl ρ b
  | .shift c a => ParametricActualCollapse.collapseWith ctrl
      (fixedHead c + (scalarValueWith ctrl ρ a : Ordinal))

noncomputable def vectorValueWith {ι : Type} {n : Nat} (ctrl : Nat → Nat)
    (v : CompiledVector ι n) (ρ : ι → Nat) : Fin (n+1) → Ordinal :=
  Fin.cases (scalarValueWith ctrl ρ v.scalar : Ordinal)
    (fun j => (v.positive j).evaluate.1.repr)

end LogicLineages.PermittedControl.SelectedGeneratedSource
