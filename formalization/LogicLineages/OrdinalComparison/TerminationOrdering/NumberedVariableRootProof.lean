module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableRootTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableRootProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedWindowEquivalence

def variableView {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q : Packed Symbol arity Gamma) : Option (Packed Symbol arity Gamma) :=
  match q.2 with
  | .var v => some ⟨_,AuxTerm.var v⟩
  | _ => none

theorem primaryVariableView {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : WindowPrimary Symbol arity symbols S Gamma q r) :
    variableView q = variableView r := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  all_goals first | rfl | trivial

theorem variableViewSound {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q r : Packed Symbol arity Gamma) (h : variableView q = some r) : q = r := by
  obtain ⟨rho,q⟩ := q
  cases q <;> simp_all [variableView]

theorem actualVariablePrimaryRigid : NumberedVariableRootTargets.ActualVariablePrimaryRigid := by
  intro Symbol arity symbols S Gamma tau v q h
  exact variableViewSound q ⟨tau,AuxTerm.var v⟩ (primaryVariableView h).symm

theorem actualVariableStepBottom : NumberedVariableRootTargets.ActualVariableStepBottom := by
  intro Symbol arity symbols S above Gamma tau v q
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst q
    exact WindowStep.bottom (.var v) (by intro h; cases h)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableRootProof
