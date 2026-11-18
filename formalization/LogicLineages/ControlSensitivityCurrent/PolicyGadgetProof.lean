module
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetTargets
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionAtomicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyGadget
open LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion ParametricSourceAddition
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem shape_pos {n : Nat} (s : AdmissibleSum.Shape n) : 0 < n := by
  induction s with
  | leaf => omega
  | join a b ha hb => omega

private theorem shape_one_aux {n : Nat} (s : AdmissibleSum.Shape n) (h : n = 1) :
    HEq s AdmissibleSum.Shape.leaf := by
  cases s with
  | leaf => rfl
  | join a b => have ha := shape_pos a; have hb := shape_pos b; omega

private theorem shape_one (s : AdmissibleSum.Shape 1) : s = .leaf :=
  eq_of_heq (shape_one_aux s rfl)

private theorem shape_two_aux {k : Nat} (s : AdmissibleSum.Shape k) (h : k = 2) :
    HEq s (AdmissibleSum.Shape.join .leaf .leaf) := by
  cases s with
  | leaf => omega
  | @join n m a b =>
    have ha := shape_pos a
    have hb := shape_pos b
    have h1 : n = 1 := by omega
    have h2 : m = 1 := by omega
    subst n
    subst m
    rw [shape_one a, shape_one b]

private theorem shape_two (s : AdmissibleSum.Shape 2) : s = .join .leaf .leaf :=
  eq_of_heq (shape_two_aux s rfl)

theorem smallShapes : PolicyGadgetTargets.SmallShapes :=
  ⟨fun _ => shape_pos, shape_one, shape_two⟩

private theorem shape0 (p : AdmissibleSum.Policy) (site : AdmissibleSum.MacroSite) :
    p.shape site 0 = .leaf := shape_one _
private theorem shape1 (p : AdmissibleSum.Policy) (site : AdmissibleSum.MacroSite) :
    p.shape site 1 = .join .leaf .leaf := shape_two _

theorem atomicEraserAssignment : PolicyGadgetTargets.AtomicEraserAssignment := by
  intro p Γ a b
  cases a <;> cases b
  all_goals
    apply congrArg some
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [Ty.level, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    simp only [AdmissibleAssignment.application, AdmissibleAssignment.box,
      Ty.level, Fin.val_zero]
    rw [ordinalBoxPositive]
    simp only [show ¬ (1 ≤ 0) by omega, dite_false]
    simp [Fin.cases_zero, eraserVector, atomExpression, AdmissibleAssignment.boxTail,
      Ty.level, ordinalVectorAt, ordinalPartialSize, ordinalHeadFree, ordinalHeadOccurs,
      ordinalHeadComponentOccurs, ordinalFreePartialVector, ordinalHeadClosure,
      ordinalHeadClosureComponent, substitute, Renaming.weaken,
      AdmissibleAssignment.repeated, shape0, shape1, AdmissibleSum.expand]
    all_goals first | rfl | exact ⟨rfl, rfl⟩

theorem successorAssignment : PolicyGadgetTargets.SuccessorAssignment := by
  intro p Γ x
  apply congrArg some
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [AdmissibleAssignment.application, AdmissibleAssignment.box,
    AdmissibleAssignment.boxTail, ordinalBoxPositive, ordinalVectorAt, Ty.level]

theorem identityZeroAssignment : PolicyGadgetTargets.IdentityZeroAssignment := by
  intro p Γ
  apply congrArg some
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp only [Ty.level, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  simp only [AdmissibleAssignment.application, AdmissibleAssignment.box,
    Ty.level, Fin.val_zero]
  rw [ordinalBoxPositive]
  simp only [show ¬ (1 ≤ 0) by omega, dite_false]
  simp [Fin.cases_zero, identityZeroVector, AdmissibleAssignment.boxTail,
    Ty.level, ordinalVectorAt, ordinalPartialSize, ordinalHeadFree, ordinalHeadOccurs,
    ordinalHeadComponentOccurs, ordinalHeadClosure, ordinalHeadClosureComponent,
    substitute, AdmissibleAssignment.repeated, shape0, shape1, AdmissibleSum.expand]
  all_goals first | rfl | exact ⟨rfl, rfl⟩

#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyGadget
end LogicLineages.ControlSensitivityCurrent.PolicyGadget
