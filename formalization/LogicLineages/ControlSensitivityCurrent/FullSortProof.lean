module
public import LogicLineages.ControlSensitivityCurrent.FullSortTargets
public import LogicLineages.ControlSensitivityCurrent.FullAdditionProof
public import LogicLineages.ControlSensitivityCurrent.PairCodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullSort
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion
open ParametricSourceSuccessor (denoteWith)
open ParametricSourceAddition.Proof (add_value collapse_one_value)

private theorem observation_exact (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (hm : StrictMono f) (hi : ∀ n : Nat, n ≤ f n) (Γ : List Ty)
    (ρ : OrdinalComponent Γ → Nat) (x : Variable Γ .ground) (y : Nat) :
    PolicySort.Observation p f ρ (successorProbe x) y ↔ y = f (input ρ x+4) := by
  let r : OrdinalComponent Γ → Ordinal := fun c => ((ρ c+1 : Nat) : Ordinal)
  have h1 : denoteWith f r (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [denoteWith]
  have hx : denoteWith f r (.var ⟨.ground,x,0⟩) = ((input ρ x+1 : Nat) : Ordinal) := rfl
  have ht := add_value f r _ _ _ _ h1 hx
  have hs := collapse_one_value f hm hi r _ _ ht
  have hn : 1 + (input ρ x+1) + 2 = input ρ x+4 := by omega
  rw [hn] at hs
  constructor
  · rintro ⟨v,hv,he⟩
    rw [PolicyGadget.successorAssignment] at hv
    cases Option.some.inj hv
    change denoteWith f r (.collapse .one (.add .one (.var ⟨.ground,x,0⟩))) = _ at he
    rw [hs] at he
    have he' : f (input ρ x+4)+1 = y+1 := by exact_mod_cast he
    omega
  · intro h
    subst y
    exact ⟨_,PolicyGadget.successorAssignment p Γ x,hs⟩

private theorem double_lt_double_exp (m : Nat) : 2*m < 2^(2^m) := by
  have h1 := m.lt_two_pow_self
  have hpow : 2^(m+1) ≤ 2^(2^m) := Nat.pow_le_pow_right (by decide) h1
  rw [pow_succ] at hpow
  omega

theorem completeSort : Targets.CompleteSort := by
  intro f hf
  have hc := FullAddition.completeAddition.2.2.2 f hf
  have hm := hc.1
  have hi := hc.2.1
  have hp : ∀ n : Nat, 0 < f (n+4) := fun n => by have := hi (n+4); omega
  have hd : ∀ n : Nat, 2*f (n+4) < f (n+1+4) := by
    intro n
    have h := (double_lt_double_exp (f (n+4))).trans_le (hf.2 (n+4))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  refine ⟨fun n => ⟨hp n,hd n⟩, PairCoding.pairCoding (fun n => f (n+4)) hp hd, ?_⟩
  intro p
  refine ⟨observation_exact p f hm (fun n => (hi n).le), ?_⟩
  intro Γ ρ a b low high difference
  unfold PolicySort.SortFormula
  simp only [observation_exact p f hm (fun n => (hi n).le)]
  rw [← PairCoding.sortedWitness (fun n => f (n+4)) hp hd
    (input ρ a) (input ρ b) (input ρ low) (input ρ high) difference]
  constructor
  · rintro ⟨qa,qb,ql,qh,rfl,rfl,rfl,rfl,hs,he⟩
    exact ⟨hs,he⟩
  · rintro ⟨hs,he⟩
    exact ⟨_,_,_,_,rfl,rfl,rfl,rfl,hs,he⟩
#audit_namespace LogicLineages.ControlSensitivityCurrent.FullSort
end LogicLineages.ControlSensitivityCurrent.FullSort
