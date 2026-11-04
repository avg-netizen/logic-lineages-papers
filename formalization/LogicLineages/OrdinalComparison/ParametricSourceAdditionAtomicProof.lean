module
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionTargets
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceAddition.Proof
open LogicLineages.ComputabilityKnowledge
open WWOrdinalTermSemantics WWOrdinalTermSemanticsProof
open SourceAdditionCompletion SourceSortCompletion
open ParametricSourceSuccessor
theorem eraser_assignment {Γ} (a b : Atom Γ) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (eraser a b) =
      some (eraserVector a b) := by
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
      AdmissibleAssignment.repeated, OrdinalSyntax.defaultPolicy,
      OrdinalSyntax.defaultShape, OrdinalSyntax.leftShape, AdmissibleSum.expand]
    all_goals first | rfl | exact ⟨rfl, rfl⟩


variable (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n : Nat, n ≤ G n)

theorem add_value {Γ} (ρ : OrdinalComponent Γ → Ordinal)
    (a b : OrdinalExpression Γ) (m n : Nat)
    (ha : denoteWith G ρ a = (m : Ordinal)) (hb : denoteWith G ρ b = (n : Ordinal)) :
    denoteWith G ρ (.add a b) = ((m+n : Nat) : Ordinal) := by
  change ordinalNaturalSum (denoteWith G ρ a) (denoteWith G ρ b) = _
  rw [ha,hb]
  exact naturalSum_finite m n

include hm hi in
theorem collapse_one_value {Γ} (ρ : OrdinalComponent Γ → Ordinal)
    (t : OrdinalExpression Γ) (n : Nat) (h : denoteWith G ρ t = (n : Ordinal)) :
    denoteWith G ρ (.collapse .one t) = ((G (n+2)+1 : Nat) : Ordinal) := by
  change (ParametricActualCollapse.collapseWith G
    (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 1) (denoteWith G ρ t)) : Ordinal) = _
  rw [h]
  have hp := WWOmegaFiniteCalibrationProof.productCalibration 1
  have hs := WWOmegaFiniteCalibrationProof.sumCalibration 1 n
  simp only [Nat.cast_one,mul_one] at hp hs
  rw [hp,hs]
  exact congrArg (fun z : Nat => (z : Ordinal))
    (ParametricCoefficientOne.Proof.genericCoefficientOne G hm hi n)

include hm hi in
theorem eraser_value {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Atom Γ) :
    denoteWith G (fun c => ((ρ c + 1 : Nat) : Ordinal)) (eraserVector a b 0) =
      ((G (3 * atomValue ρ a + atomValue ρ b + 8) + 1 : Nat) : Ordinal) := by
  let r : OrdinalComponent Γ → Ordinal := fun c => ((ρ c + 1 : Nat) : Ordinal)
  have ha : denoteWith G r (atomExpression a) = ((atomValue ρ a + 1 : Nat) : Ordinal) := by
    cases a <;> simp [atomExpression, atomValue, denoteWith, r, input]
  have hb : denoteWith G r (atomExpression b) = ((atomValue ρ b + 1 : Nat) : Ordinal) := by
    cases b <;> simp [atomExpression, atomValue, denoteWith, r, input]
  have h1 : denoteWith G r (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [denoteWith]
  have ha1 := add_value G r _ _ _ _ ha h1
  have haa := add_value G r _ _ _ _ ha1 ha1
  have haaa := add_value G r _ _ _ _ haa ha
  have ht := add_value G r _ _ _ _ haaa hb
  have hh := collapse_one_value G hm hi r _ _ ht
  have hn : atomValue ρ a + 1 + 1 + (atomValue ρ a + 1 + 1) +
      (atomValue ρ a + 1) + (atomValue ρ b + 1) + 2 =
      3 * atomValue ρ a + atomValue ρ b + 8 := by omega
  simpa only [hn, eraserVector, r] using hh


theorem atomicAssignmentValue : Targets.AtomicAssignmentValue := by
  intro G hm hi Γ ρ a b
  exact ⟨eraser_assignment a b,eraser_value G hm hi ρ a b⟩
end LogicLineages.OrdinalComparison.Source.ParametricSourceAddition.Proof
