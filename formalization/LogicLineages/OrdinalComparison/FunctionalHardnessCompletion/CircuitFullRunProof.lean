module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullTargets
public import Mathlib.Data.List.Enum
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
open LogicLineages.ComputabilityKnowledge.CircuitReduction
open LogicLineages.ComputabilityKnowledge.PositiveExpression

/-- The recursive sequence of equations is exactly the builder's indexed list. -/
theorem gatesHold_iff_get (n : Nat) (gs : List Gate) (v : Nat → Nat) :
    GatesHold n gs v ↔ ∀ (i : Nat) (hi : i<gs.length), v (n+i)=gateValue v gs[i] := by
  induction gs generalizing n with
  | nil => simp [GatesHold]
  | cons g gs ih =>
      constructor
      · rintro ⟨hg,hgs⟩ i hi
        cases i with
        | zero => simpa using hg
        | succ i =>
            have he := (ih (n+1)).mp hgs i (by simpa using hi)
            simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he
      · intro h
        refine ⟨?_,(ih (n+1)).mpr ?_⟩
        · exact h 0 (by simp)
        · intro i hi
          have he := h (i+1) (by simpa using hi)
          simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he

theorem gatesHold_iff_zipIdx (n : Nat) (gs : List Gate) (v : Nat → Nat) :
    GatesHold n gs v ↔ ∀ gi∈gs.zipIdx, v (n+gi.2)=gateValue v gi.1 := by
  rw [gatesHold_iff_get]
  constructor
  · intro h
    exact List.forall_mem_zipIdx'.mpr h
  · intro h
    exact List.forall_mem_zipIdx'.mp h

theorem valid_get (n : Nat) (gs : List Gate) (hv : ValidFrom n gs)
    (i : Nat) (hi : i<gs.length) : gs[i].ValidAt (n+i) := by
  induction gs generalizing n i with
  | nil => simp at hi
  | cons g gs ih =>
      obtain ⟨hg,hgs⟩ := hv
      cases i with
      | zero => simpa using hg
      | succ i =>
          have h := ih (n+1) hgs i (by simpa using hi)
          simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

private theorem gateValue_congr (g : Gate) (n : Nat) (v w : Nat → Nat)
    (hg : g.ValidAt n) (h : ∀ j, j<n → v j=w j) : gateValue v g=gateValue w g := by
  cases g with
  | constant k => rfl
  | add x y => exact congrArg₂ Nat.add (h x hg.1) (h y hg.2)
  | mul x y => exact congrArg₂ Nat.mul (h x hg.1) (h y hg.2)

private theorem gate_eval_value (g : Gate) (ρ : Nat → PosNat) :
    (g.eval ρ).val=gateValue (fun i => (ρ i).val) g := by cases g <;> rfl

private theorem run_below (gs : List Gate) (n : Nat) (ρ : Nat → PosNat)
    (j : Nat) (hj : j<n) : run n gs ρ j=ρ j := by
  induction gs generalizing n ρ with
  | nil => rfl
  | cons g gs ih =>
      rw [run,ih (n+1) (assign ρ n (g.eval ρ)) (by omega)]
      simp [assign,show j≠n by omega]

private theorem run_correct (gs : List Gate) (n : Nat) (ρ : Nat → PosNat)
    (hv : ValidFrom n gs) : GatesHold n gs (fun i => (run n gs ρ i).val) := by
  induction gs generalizing n ρ with
  | nil => trivial
  | cons g gs ih =>
      obtain ⟨hg,hgs⟩ := hv
      let η := assign ρ n (g.eval ρ)
      have hb : ∀ j, j<n → (run (n+1) gs η j).val=(ρ j).val := by
        intro j hj
        rw [run_below gs (n+1) η j (by omega)]
        simp [η,assign,show j≠n by omega]
      have he := gateValue_congr g n (fun j => (run (n+1) gs η j).val)
        (fun j => (ρ j).val) hg hb
      change (run (n+1) gs η n).val=gateValue (fun j => (run (n+1) gs η j).val) g ∧ _
      constructor
      · rw [run_below gs (n+1) η n (by omega),he]
        simpa [η,assign] using gate_eval_value g ρ
      · exact ih (n+1) η hgs

private theorem run_of_correct (gs : List Gate) (n : Nat) (ρ : Nat → PosNat)
    (h : GatesHold n gs (fun i => (ρ i).val)) : run n gs ρ=ρ := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
      obtain ⟨hg,hgs⟩ := h
      have he : ρ n=g.eval ρ := Subtype.ext (hg.trans (gate_eval_value g ρ).symm)
      have ha : assign ρ n (g.eval ρ)=ρ := by
        funext j
        by_cases hj : j=n
        · simp [assign,hj,←he]
        · simp [assign,hj]
      rw [run,ha]
      exact ih (n+1) hgs

private theorem gates_positive (gs : List Gate) (n : Nat) (v : Nat → Nat)
    (hv : ValidFrom n gs) (h : GatesHold n gs v) (hin : ∀ j,j<n → 0<v j) :
    ∀ j,j<n+gs.length → 0<v j := by
  induction gs generalizing n with
  | nil => simpa using hin
  | cons g gs ih =>
      obtain ⟨hg,hgs⟩ := hv
      obtain ⟨he,hes⟩ := h
      have hn : 0<v n := by
        rw [he]
        cases g with
        | constant k => simp [gateValue]
        | add x y => exact Nat.add_pos_left (hin x hg.1) _
        | mul x y => exact Nat.mul_pos (hin x hg.1) (hin y hg.2)
      have hin' : ∀ j,j<n+1 → 0<v j := by
        intro j hj
        by_cases he : j=n
        · simpa [he] using hn
        · exact hin j (by omega)
      intro j hj
      exact ih (n+1) hgs hes hin' j (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj)

private theorem gatesHold_congr (gs : List Gate) (n : Nat) (v w : Nat → Nat)
    (hv : ValidFrom n gs) (h : ∀ j,j<n+gs.length → w j=v j)
    (he : GatesHold n gs v) : GatesHold n gs w := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
      obtain ⟨hg,hgs⟩ := hv
      obtain ⟨he,hes⟩ := he
      constructor
      · rw [h n (by simp <;> omega),he]
        exact (gateValue_congr g n w v hg (fun j hj => h j (by simp <;> omega))).symm
      · exact ih (n+1) hgs (fun j hj => h j (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj)) hes

theorem scalar_run_semantics : Targets.ScalarRunSemantics := by
  intro c hc
  obtain ⟨hv,hl,hr⟩ := hc
  constructor
  · rintro ⟨ρ,he⟩
    exact ⟨(fun i => (run c.inputCount c.gates ρ i).val),
      (fun i _ => (run c.inputCount c.gates ρ i).property),
      run_correct c.gates c.inputCount ρ hv,he⟩
  · rintro ⟨v,hin,hg,he⟩
    have hp := gates_positive c.gates c.inputCount v hv hg hin
    let ρ : Nat → PosNat := fun i => if h : 0<v i then ⟨v i,h⟩ else ⟨1,by decide⟩
    have hρ : ∀ i,i<c.inputCount+c.gates.length → (ρ i).val=v i := by
      intro i hi
      simp [ρ,hp i hi]
    have hgc : GatesHold c.inputCount c.gates (fun i => (ρ i).val) :=
      gatesHold_congr c.gates c.inputCount v _ hv hρ hg
    refine ⟨ρ,?_⟩
    unfold Circuit.outputEqual
    rw [run_of_correct c.gates c.inputCount ρ hgc,hρ c.leftOutput hl,hρ c.rightOutput hr]
    exact he

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
