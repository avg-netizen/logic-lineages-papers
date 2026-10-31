module
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionTargets
public import LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibrationProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.ElementaryControl
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
open LogicLineages.ComputabilityKnowledge
open WWOrdinalTermSemantics WWOrdinalTermSemanticsProof
open SourceSortCompletion

private def atomExpression {Γ} : Atom Γ → OrdinalExpression Γ
  | .zero => .one
  | .var x => .var ⟨.ground, x, 0⟩
private def atomValue {Γ} (ρ : OrdinalComponent Γ → Nat) : Atom Γ → Nat
  | .zero => 0
  | .var x => input ρ x
private def eraserVector {Γ} (a b : Atom Γ) : OrdinalVector Γ 0 := fun _ =>
  .collapse .one (.add
    (.add (.add (.add (atomExpression a) .one) (.add (atomExpression a) .one))
      (atomExpression a)) (atomExpression b))

private theorem eraser_assignment {Γ} (a b : Atom Γ) :
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

theorem add_value {Γ} (ρ : OrdinalComponent Γ → Ordinal)
    (a b : OrdinalExpression Γ) (m n : Nat)
    (ha : denote ρ a = (m : Ordinal)) (hb : denote ρ b = (n : Ordinal)) :
    denote ρ (.add a b) = ((m+n : Nat) : Ordinal) := by
  change ordinalNaturalSum (denote ρ a) (denote ρ b) = _
  rw [ha, hb]
  exact naturalSum_finite m n

theorem collapse_one_value {Γ} (ρ : OrdinalComponent Γ → Ordinal)
    (t : OrdinalExpression Γ) (n : Nat) (h : denote ρ t = (n : Ordinal)) :
    denote ρ (.collapse .one t) = ((Phi (n+2)+1 : Nat) : Ordinal) := by
  change (actualCollapse (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 1)
    (denote ρ t)) : Ordinal) = _
  rw [h]
  have hp := WWOmegaFiniteCalibrationProof.productCalibration 1
  have hs := WWOmegaFiniteCalibrationProof.sumCalibration 1 n
  simp only [Nat.cast_one] at hp hs
  rw [hp, hs]
  simpa [Nat.add_comm] using congrArg (fun z : Nat => (z : Ordinal)) (actualFiniteHeadCollapse 1 n)

/-- Fixed finite-head injectivity kept symbolic, avoiding closed giant values. -/
theorem collapse_one_equal {Γ} (ρ : OrdinalComponent Γ → Ordinal)
    (t s : OrdinalExpression Γ) (n m : Nat)
    (ht : denote ρ t = (n : Ordinal)) (hs : denote ρ s = (m : Ordinal)) :
    denote ρ (.collapse .one t) = denote ρ (.collapse .one s) ↔ n = m := by
  rw [collapse_one_value ρ t n ht, collapse_one_value ρ s m hs]
  constructor
  · intro h
    have hn : Phi (n+2)+1 = Phi (m+2)+1 := Nat.cast_injective h
    have hp : Phi (n+2) = Phi (m+2) := by omega
    have := Phi_strictMono.injective hp
    omega
  · intro h
    rw [h]

private theorem eraser_value {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Atom Γ) :
    denote (fun c => ((ρ c + 1 : Nat) : Ordinal)) (eraserVector a b 0) =
      ((Phi (3 * atomValue ρ a + atomValue ρ b + 8) + 1 : Nat) : Ordinal) := by
  let r : OrdinalComponent Γ → Ordinal := fun c => ((ρ c + 1 : Nat) : Ordinal)
  have ha : denote r (atomExpression a) = ((atomValue ρ a + 1 : Nat) : Ordinal) := by
    cases a <;> simp [atomExpression, atomValue, denote, r, input]
  have hb : denote r (atomExpression b) = ((atomValue ρ b + 1 : Nat) : Ordinal) := by
    cases b <;> simp [atomExpression, atomValue, denote, r, input]
  have h1 : denote r (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [denote]
  have ha1 := add_value r _ _ _ _ ha h1
  have haa := add_value r _ _ _ _ ha1 ha1
  have haaa := add_value r _ _ _ _ haa ha
  have ht := add_value r _ _ _ _ haaa hb
  have hh := collapse_one_value r _ _ ht
  have hn : atomValue ρ a + 1 + 1 + (atomValue ρ a + 1 + 1) +
      (atomValue ρ a + 1) + (atomValue ρ b + 1) + 2 =
      3 * atomValue ρ a + atomValue ρ b + 8 := by omega
  simpa only [hn, eraserVector, r] using hh

private theorem eraser_equation {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Atom Γ) :
    Equation ρ (eraser a b) (eraser c d) ↔
      3 * atomValue ρ a + atomValue ρ b = 3 * atomValue ρ c + atomValue ρ d := by
  constructor
  · rintro ⟨va, vb, ha, hb, he⟩
    rw [eraser_assignment] at ha hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    rw [eraser_value, eraser_value] at he
    have hn : Phi (3 * atomValue ρ a + atomValue ρ b + 8) + 1 =
        Phi (3 * atomValue ρ c + atomValue ρ d + 8) + 1 := by exact_mod_cast he
    have hphi : Phi (3 * atomValue ρ a + atomValue ρ b + 8) =
        Phi (3 * atomValue ρ c + atomValue ρ d + 8) := by omega
    have := Phi_strictMono.injective hphi
    omega
  · intro h
    refine ⟨_, _, eraser_assignment a b, eraser_assignment c d, ?_⟩
    rw [eraser_value, eraser_value, h]

theorem add_witness {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) (d : Nat) :
    AddWitness ρ a b c d ↔ input ρ a + input ρ b = input ρ c ∧ d = 3 * input ρ b := by
  simp only [AddWitness, eraser_equation, atomValue, input, extend]
  omega

theorem add_formula {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) :
    AddFormula ρ a b c ↔ input ρ a + input ρ b = input ρ c := by
  simp [AddFormula, add_witness]

theorem add_values (a b c : Nat) : AddValues a b c ↔ a+b=c := by
  exact add_formula (tripleVal a b c) .here (.there .here) (.there (.there .here))

end LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
