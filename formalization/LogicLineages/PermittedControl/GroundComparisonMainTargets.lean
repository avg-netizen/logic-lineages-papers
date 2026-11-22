module
public import LogicLineages.PermittedControl.GroundComparisonTargets
public import LogicLineages.PermittedControl.ControlTargets
public import LogicLineages.PermittedControl.Targets
public import LogicLineages.PermittedControl.SelectedFunctionalHardnessTargets

@[expose] public section
namespace LogicLineages.PermittedControl.GroundComparisonMain

/-- Comparator for Paper 17 `thm:main` (Comparison classification):
the literal control laws of both controls (`lem:control`: even, primitive
recursive, `≥ G`, the separation growth, an eventual finite-level bound, the
modular decrement), the prefix and distance clauses of `f_b`
(`f_b = G` on `[0,b]`, `G ≤ f_b`, `f_b − G < 2·lcm(1..n)` after `b`), clause (i)
as `thm:ground` for both controls and every effective policy, and clauses
(ii)–(iii) as `thm:functional-hardness` for both controls and every policy. -/
def MainComparison : Prop :=
  Targets.FullControl ∧ Targets.NearControlModular ∧ GroundComparison.GroundComparison ∧
    SelectedFunctionalHardnessTargets.SelectedFunctionalHardness

end LogicLineages.PermittedControl.GroundComparisonMain
