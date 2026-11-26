module
public import LogicLineages.ControlSensitivityCurrent.PolicyAdditionTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetProof
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionAtomicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyAddition
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion
open ParametricSourceAddition (atomValue eraserVector)
open ParametricSourceSuccessor (denoteWith)
open ParametricSourceAddition.Proof (eraser_value add_value collapse_one_value)
variable (p : AdmissibleSum.Policy) (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n : Nat, n ≤ G n)
include hm hi in
theorem weighted_equality {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Atom Γ) :
    Equation p G ρ (eraser a b) (eraser c d) ↔
      3 * atomValue ρ a + atomValue ρ b = 3 * atomValue ρ c + atomValue ρ d := by
  constructor
  · rintro ⟨va, vb, ha, hb, he⟩
    rw [PolicyGadget.atomicEraserAssignment] at ha hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    rw [eraser_value G hm hi, eraser_value G hm hi] at he
    have hn : G (3 * atomValue ρ a + atomValue ρ b + 8) + 1 =
        G (3 * atomValue ρ c + atomValue ρ d + 8) + 1 := by exact_mod_cast he
    have hphi : G (3 * atomValue ρ a + atomValue ρ b + 8) =
        G (3 * atomValue ρ c + atomValue ρ d + 8) := by omega
    have := hm.injective hphi
    omega
  · intro h
    refine ⟨_, _, PolicyGadget.atomicEraserAssignment p _ a b, PolicyGadget.atomicEraserAssignment p _ c d, ?_⟩
    rw [eraser_value G hm hi, eraser_value G hm hi, h]

include hm hi in
theorem add_witness {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) (d : Nat) :
    AddWitness p G ρ a b c d ↔ input ρ a + input ρ b = input ρ c ∧ d = 3 * input ρ b := by
  simp only [AddWitness, weighted_equality p G hm hi, atomValue, input, extend]
  omega

include hm hi in
theorem add_formula {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) :
    AddFormula p G ρ a b c ↔ input ρ a + input ρ b = input ρ c := by
  simp [AddFormula, add_witness p G hm hi]



theorem exactAddition : PolicyAdditionTargets.ExactAddition := by
  intro p G hm hi Γ ρ a b c
  exact ⟨add_witness p G hm hi ρ a b c, add_formula p G hm hi ρ a b c⟩

include hm hi in
private theorem successor_identity {Γ} (ρ : OrdinalComponent Γ → Nat) (x : Variable Γ .ground) :
    Equation p G ρ (successorProbe x) (.app identity .zeroC) ↔ input ρ x = 2 := by
  let r : OrdinalComponent Γ → Ordinal := fun c => ((ρ c + 1 : Nat) : Ordinal)
  have h1 : denoteWith G r (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [denoteWith]
  have hx : denoteWith G r (.var ⟨.ground,x,0⟩) = ((input ρ x + 1 : Nat) : Ordinal) := rfl
  have ht := add_value G r _ _ _ _ h1 hx
  have h2 := add_value G r _ _ _ _ h1 h1
  have h3 := add_value G r _ _ _ _ h2 h1
  have h4 := add_value G r _ _ _ _ h3 h1
  have hs := collapse_one_value G hm hi r _ _ ht
  have hz := collapse_one_value G hm hi r _ _ h4
  constructor
  · rintro ⟨va,vb,ha,hb,he⟩
    rw [PolicyGadget.successorAssignment] at ha
    rw [PolicyGadget.identityZeroAssignment] at hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    change denoteWith G r (.collapse .one (.add .one (.var ⟨.ground,x,0⟩))) =
      denoteWith G r (.collapse .one (.add (.add (.add .one .one) .one) .one)) at he
    rw [hs,hz] at he
    have hn : G (1 + (input ρ x + 1) + 2) + 1 = G (1+1+1+1+2)+1 := by exact_mod_cast he
    have hg : G (1 + (input ρ x + 1) + 2) = G (1+1+1+1+2) := by omega
    have := hm.injective hg
    omega
  · intro h
    refine ⟨_,_,PolicyGadget.successorAssignment p Γ x,PolicyGadget.identityZeroAssignment p Γ,?_⟩
    change denoteWith G r (.collapse .one (.add .one (.var ⟨.ground,x,0⟩))) =
      denoteWith G r (.collapse .one (.add (.add (.add .one .one) .one) .one))
    rw [hs,hz,h]

theorem exactOne : PolicyAdditionTargets.ExactOne := by
  intro p G hm hi u
  simp only [OneFormula, successor_identity p G hm hi, add_formula p G hm hi,
    input, extend, singletonVal]
  constructor
  · rintro ⟨v,hv,hu⟩; omega
  · intro h; subst u; exact ⟨2,rfl,rfl⟩

include hm hi in
private theorem add_values (a b c : Nat) : AddValues p G a b c ↔ a+b=c := by
  simp only [AddValues, add_formula p G hm hi, tripleVal, input, extend, singletonVal]

include hm hi in
theorem dag_correct (k : Nat) :
    (binaryDAG k).gates ≤ 2 * (Nat.log2 k + 1) ∧
    ∀ y : Nat, Run p G (binaryDAG k) y ↔ y = k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 2
    · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;>
        simp [binaryDAG, BinaryDAG.gates, Run]
    · have hdiv : k / 2 < k := Nat.div_lt_self (by omega) (by omega)
      have child := ih (k / 2) hdiv
      have hn : k >>> 1 ≠ 0 := by simp only [Nat.shiftRight_eq_div_pow]; omega
      have hlog : Nat.log2 k = Nat.log2 (k / 2) + 1 := by
        simpa only [Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.succ_eq_add_one] using
          Nat.log2_eq_succ_log2_shiftRight hn
      have hrem := Nat.mod_add_div k 2
      rw [binaryDAG, dif_neg hk]
      split_ifs with hmod
      · constructor
        · simp only [BinaryDAG.gates]
          omega
        · intro y
          simp only [Run, child.2, add_values p G hm hi]
          constructor
          · rintro ⟨x, rfl, hy⟩
            omega
          · intro hy
            exact ⟨k / 2, rfl, by omega⟩
      · constructor
        · simp only [BinaryDAG.gates]
          omega
        · intro y
          simp only [Run, child.2, add_values p G hm hi]
          constructor
          · rintro ⟨x, z, rfl, hz, hy⟩
            omega
          · intro hy
            exact ⟨k / 2, 2 * (k / 2), rfl, by omega, by omega⟩


theorem exactBinaryDAG : PolicyAdditionTargets.ExactBinaryDAG := by
  intro p G hm hi k
  exact dag_correct p G hm hi k
#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyAddition
end LogicLineages.ControlSensitivityCurrent.PolicyAddition
