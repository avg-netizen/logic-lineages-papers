module

public import LogicLineages.ComputabilityKnowledge.Comparators.CircuitReduction
public import LogicLineages.ComputabilityKnowledge.MultiplicationGadgetProof

@[expose] public section

/-! External Codex continuation proof for the independently frozen finite-circuit
semantic comparator. This does not discharge its separate effectivity target. -/
namespace LogicLineages.ComputabilityKnowledge.CircuitReductionProof

open PositiveExpression CircuitReduction
open Comparators.ExponentialGap

private theorem congrNat2 (f : Nat → Nat → Nat) {a b c d : Nat}
    (h : a = b) (k : c = d) : f a c = f b d := by
  cases h
  cases k
  rfl

def GatesCorrect : Nat → List Gate → (Nat → PosNat) → Prop
  | _, [], _ => True
  | next, g :: gs, ρ => ρ next = g.eval ρ ∧ GatesCorrect (next + 1) gs ρ

private theorem gate_eval_congr (g : Gate) (n : Nat) (ρ τ : Nat → PosNat)
    (hg : g.ValidAt n) (h : ∀ j, j < n → ρ j = τ j) : g.eval ρ = g.eval τ := by
  cases g with
  | constant k => rfl
  | add x y => simp only [Gate.ValidAt] at hg; simp [Gate.eval, h x hg.1, h y hg.2]
  | mul x y => simp only [Gate.ValidAt] at hg; simp [Gate.eval, h x hg.1, h y hg.2]

private theorem run_below (gs : List Gate) (n : Nat) (ρ : Nat → PosNat)
    (j : Nat) (hj : j < n) : run n gs ρ j = ρ j := by
  induction gs generalizing n ρ with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih (n + 1) (assign ρ n (g.eval ρ)) (by omega)]
    simp [assign, show j ≠ n by omega]

private theorem run_congr (gs : List Gate) (n : Nat) (ρ τ : Nat → PosNat)
    (hv : ValidFrom n gs) (h : ∀ j, j < n → ρ j = τ j) :
    ∀ j, j < n + gs.length → run n gs ρ j = run n gs τ j := by
  induction gs generalizing n ρ τ with
  | nil => simpa [run] using h
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := hv
    have he := gate_eval_congr g n ρ τ hg h
    have ha : ∀ j, j < n + 1 → assign ρ n (g.eval ρ) j = assign τ n (g.eval τ) j := by
      intro j hj
      by_cases hjn : j = n
      · simp [assign, hjn, he]
      · simp [assign, hjn, h j (by omega)]
    intro j hj
    exact ih (n + 1) _ _ hgs ha j (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)

private theorem run_correct (gs : List Gate) (n : Nat) (ρ : Nat → PosNat)
    (hv : ValidFrom n gs) : GatesCorrect n gs (run n gs ρ) := by
  induction gs generalizing n ρ with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := hv
    let η := assign ρ n (g.eval ρ)
    have hb : ∀ j, j < n → run (n + 1) gs η j = ρ j := by
      intro j hj
      rw [run_below gs (n + 1) η j (by omega)]
      simp [η, assign, show j ≠ n by omega]
    have he := gate_eval_congr g n (run (n + 1) gs η) ρ hg hb
    change run (n + 1) gs η n = g.eval (run (n + 1) gs η) ∧ _
    constructor
    · rw [run_below gs (n + 1) η n (by omega), he]
      simp [η, assign]
    · exact ih (n + 1) η hgs

private theorem run_of_correct (gs : List Gate) (n : Nat) (ρ : Nat → PosNat)
    (h : GatesCorrect n gs ρ) : run n gs ρ = ρ := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := h
    have ha : assign ρ n (g.eval ρ) = ρ := by
      funext j
      by_cases hjn : j = n
      · simp [assign, hjn, ← hg]
      · simp [assign, hjn]
    rw [run, ha]
    exact ih (n + 1) hgs

private theorem numeral_eval (k : Nat) (ρ : Nat → PosNat) :
    (positiveNumeral k).eval ρ = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [positiveNumeral, Expr.eval, ih]

private theorem numeral_depth (k : Nat) : (positiveNumeral k).depth = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [positiveNumeral, Expr.depth, ih]

private theorem numeral_bounded (k b : Nat) : Bounded b (positiveNumeral k) := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ih, trivial⟩

private theorem eval_congr_bounded (e : Expr Nat) (b : Nat) (ρ τ : Nat → PosNat)
    (he : Bounded b e) (h : ∀ j, j < b → ρ j = τ j) : e.eval ρ = e.eval τ := by
  induction e with
  | one => rfl
  | var j => exact congrArg Subtype.val (h j he)
  | add a c ha hc => exact congrNat2 Nat.add (ha he.1) (hc he.2)
  | emul a c ha hc =>
    exact congrNat2 Nat.mul (congrArg (fun n : Nat => 2 ^ n) (ha he.1)) (hc he.2)

private theorem rename_bounded {ι : Type} (e : Expr ι) (f : ι → Nat) (b : Nat)
    (h : ∀ j, f j < b) : Bounded b (e.rename f) := by
  induction e with
  | one => trivial
  | var j => exact h j
  | add a c ha hc => exact ⟨ha, hc⟩
  | emul a c ha hc => exact ⟨ha, hc⟩

private theorem gate_bounded (g : Gate) (wire base i : Nat)
    (hg : g.ValidAt wire) (hw : wire < base) :
    ∀ p ∈ gateEquations wire base i g,
      Bounded (base + 8 * i + 8) p.1 ∧ Bounded (base + 8 * i + 8) p.2 := by
  cases g with
  | constant k =>
    intro p hp
    simp only [gateEquations, List.mem_singleton] at hp
    subst p
    exact ⟨by change wire < _; omega, numeral_bounded _ _⟩
  | add x y =>
    intro p hp
    simp only [gateEquations, List.mem_singleton] at hp
    subst p
    obtain ⟨hx, hy⟩ := hg
    exact ⟨by change wire < _; omega, by change x < _ ∧ y < _; omega⟩
  | mul x y =>
    intro p hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    have hn : ∀ v, gadgetNames x y wire base i v < base + 8 * i + 8 := by
      obtain ⟨hx, hy⟩ := hg
      intro v
      cases v <;> simp only [gadgetNames, auxiliary] <;> omega
    exact ⟨rename_bounded _ _ _ hn, rename_bounded _ _ _ hn⟩

private theorem bounded_mono (e : Expr Nat) (a b : Nat) (hab : a ≤ b)
    (h : Bounded a e) : Bounded b e := by
  induction e with
  | one => trivial
  | var i => change i < b; exact Nat.lt_of_lt_of_le h hab
  | add e f he hf => exact ⟨he h.1, hf h.2⟩
  | emul e f he hf => exact ⟨he h.1, hf h.2⟩

private theorem gate_depth (g : Gate) (wire base i : Nat) :
    ∀ p ∈ gateEquations wire base i g, p.1.depth ≤ 1 ∧ p.2.depth ≤ 1 := by
  cases g with
  | constant k =>
    intro p hp
    simp only [gateEquations, List.mem_singleton] at hp
    subst p
    simp [Expr.depth, numeral_depth]
  | add x y =>
    intro p hp
    simp only [gateEquations, List.mem_singleton] at hp
    subst p
    simp [Expr.depth]
  | mul x y =>
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa only [depth_rename] using MultiplicationGadgetProof.sourceDepth q hq

private theorem gadget_valuation (ρ : Nat → PosNat) (x y w base i : Nat) :
    ρ ∘ gadgetNames x y w base i = Comparators.MultiplicationGadget.valuation (ρ x) (ρ y) (ρ w)
      (ρ (auxiliary base i 0)) (ρ (auxiliary base i 1))
      (ρ (auxiliary base i 2)) (ρ (auxiliary base i 3))
      (ρ (auxiliary base i 4)) (ρ (auxiliary base i 5))
      (ρ (auxiliary base i 6)) (ρ (auxiliary base i 7)) := by
  funext v
  cases v <;> rfl

private theorem gate_sound (g : Gate) (wire base i : Nat) (ρ : Nat → PosNat)
    (h : AllEquations ρ (gateEquations wire base i g)) : ρ wire = g.eval ρ := by
  cases g with
  | constant k =>
    have he := h (.var wire, positiveNumeral k) (by simp [gateEquations])
    apply Subtype.ext
    simpa only [Expr.eval, numeral_eval, Gate.eval] using he
  | add x y =>
    have he := h (.var wire, .add (.var x) (.var y)) (by simp [gateEquations])
    exact Subtype.ext he
  | mul x y =>
    have hs : Comparators.MultiplicationGadget.SourceEquations (ρ ∘ gadgetNames x y wire base i) := by
      intro q hq
      have he := h (q.1.rename (gadgetNames x y wire base i),
        q.2.rename (gadgetNames x y wire base i)) (List.mem_map.mpr ⟨q, hq, rfl⟩)
      simpa only [eval_rename] using he
    rw [gadget_valuation] at hs
    have hn := (MultiplicationGadgetProof.sourceCorr _ _ _ _ _ _ _ _ _ _ _).mp hs
    have hm := (MultiplicationGadgetProof.numerical (ρ x) (ρ y) (ρ wire)).mpr
      ⟨_, _, _, _, _, _, _, _, hn⟩
    exact Subtype.ext hm

private theorem gates_sound (gs : List Gate) (next base i : Nat) (ρ : Nat → PosNat)
    (h : AllEquations ρ (compileGates base next i gs)) : GatesCorrect next gs ρ := by
  induction gs generalizing next i with
  | nil => trivial
  | cons g gs ih =>
    constructor
    · apply gate_sound g next base i ρ
      intro p hp
      exact h p (List.mem_append_left _ hp)
    · apply ih (next + 1) (i + 1)
      intro p hp
      exact h p (List.mem_append_right _ hp)

private def suffix (ρ : Nat → PosNat) (start : Nat) (values : Nat → PosNat) : Nat → PosNat :=
  fun j => if j < start then ρ j else values (j - start)

private theorem suffix_below (ρ : Nat → PosNat) (start : Nat) (values : Nat → PosNat)
    (j : Nat) (hj : j < start) : suffix ρ start values j = ρ j := by
  simp [suffix, hj]

private theorem suffix_at (ρ : Nat → PosNat) (start : Nat) (values : Nat → PosNat)
    (j : Nat) : suffix ρ start values (start + j) = values j := by
  simp [suffix, show ¬ start + j < start by omega]

private theorem realize_gate (g : Gate) (wire base i : Nat) (ρ : Nat → PosNat)
    (hg : g.ValidAt wire) (hw : wire < base) (hc : ρ wire = g.eval ρ) :
    ∃ τ : Nat → PosNat, (∀ j, j < base + 8 * i → τ j = ρ j) ∧
      AllEquations τ (gateEquations wire base i g) := by
  cases g with
  | constant k =>
    refine ⟨ρ, fun _ _ => rfl, ?_⟩
    intro p hp
    simp only [gateEquations, List.mem_singleton] at hp
    subst p
    have hval := congrArg Subtype.val hc
    simpa only [Expr.eval, numeral_eval, Gate.eval] using hval
  | add x y =>
    refine ⟨ρ, fun _ _ => rfl, ?_⟩
    intro p hp
    simp only [gateEquations, List.mem_singleton] at hp
    subst p
    exact congrArg Subtype.val hc
  | mul x y =>
    obtain ⟨hx, hy⟩ := hg
    have hm : (ρ wire).val = (ρ x).val * (ρ y).val := congrArg Subtype.val hc
    obtain ⟨s,t,u,v,q,r,h,k, hnum⟩ := (MultiplicationGadgetProof.numerical _ _ _).mp hm
    let values : Nat → PosNat := fun j => match j with
      | 0 => s | 1 => t | 2 => u | 3 => v | 4 => q | 5 => r | 6 => h | _ => k
    let τ := suffix ρ (base + 8 * i) values
    have ht : ∀ j, j < base + 8 * i → τ j = ρ j :=
      fun j hj => suffix_below ρ _ values j hj
    have hnames : τ ∘ gadgetNames x y wire base i = Comparators.MultiplicationGadget.valuation (ρ x) (ρ y) (ρ wire) s t u v q r h k := by
      funext z
      cases z <;> simp only [Function.comp_apply, gadgetNames, Comparators.MultiplicationGadget.valuation, auxiliary]
      · exact ht x (by omega)
      · exact ht y (by omega)
      · exact ht wire (by omega)
      all_goals change suffix ρ (base + 8 * i) values ((base + 8 * i) + _) = _
      all_goals rw [suffix_at]
      all_goals rfl
    refine ⟨τ, ht, ?_⟩
    have hsource := (MultiplicationGadgetProof.sourceCorr _ _ _ _ _ _ _ _ _ _ _).mpr hnum
    intro p hp
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hp
    simp only [eval_rename]
    rw [hnames]
    exact hsource pair hpair

private theorem correct_congr (gs : List Gate) (next bound : Nat) (ρ τ : Nat → PosNat)
    (hv : ValidFrom next gs) (hb : next + gs.length ≤ bound)
    (h : ∀ j, j < bound → τ j = ρ j) (hc : GatesCorrect next gs ρ) : GatesCorrect next gs τ := by
  induction gs generalizing next with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := hv
    obtain ⟨hc, hcs⟩ := hc
    constructor
    · rw [h next (by simp only [List.length_cons] at hb; omega), hc]
      exact (gate_eval_congr g next τ ρ hg (fun j hj => h j (by omega))).symm
    · exact ih (next + 1) hgs (by simp only [List.length_cons] at hb; omega) hcs

private theorem realize_gates (gs : List Gate) (next base i : Nat) (ρ : Nat → PosNat)
    (hv : ValidFrom next gs) (hb : next + gs.length ≤ base)
    (hc : GatesCorrect next gs ρ) :
    ∃ τ : Nat → PosNat, (∀ j, j < base + 8 * i → τ j = ρ j) ∧
      AllEquations τ (compileGates base next i gs) := by
  induction gs generalizing next i ρ with
  | nil => exact ⟨ρ, fun _ _ => rfl, by intro p hp; cases hp⟩
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := hv
    obtain ⟨hc, hcs⟩ := hc
    have hw : next < base := by simp only [List.length_cons] at hb; omega
    obtain ⟨η, he, hs⟩ := realize_gate g next base i ρ hg hw hc
    have hcs' : GatesCorrect (next + 1) gs η :=
      correct_congr gs (next + 1) base ρ η hgs
        (by simp only [List.length_cons] at hb; omega)
        (fun j hj => he j (by omega)) hcs
    obtain ⟨τ, ht, htail⟩ := ih (next + 1) (i + 1) η hgs
      (by simp only [List.length_cons] at hb; omega) hcs'
    refine ⟨τ, ?_, ?_⟩
    · intro j hj
      rw [ht j (by omega), he j hj]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨hl, hr⟩ := gate_bounded g next base i hg hw p hp
        have hpres : ∀ j, j < base + 8 * i + 8 → τ j = η j := fun j hj => ht j (by omega)
        rw [eval_congr_bounded p.1 _ τ η hl hpres,
          eval_congr_bounded p.2 _ τ η hr hpres]
        exact hs p hp
      · exact htail p hp

private theorem compiled_depth (gs : List Gate) (next base i : Nat) :
    ∀ p ∈ compileGates base next i gs, p.1.depth ≤ 1 ∧ p.2.depth ≤ 1 := by
  induction gs generalizing next i with
  | nil => intro p hp; cases hp
  | cons g gs ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact gate_depth g next base i p hp
    · exact ih (next + 1) (i + 1) p hp

private theorem compiled_bounded (gs : List Gate) (next base i bound : Nat)
    (hv : ValidFrom next gs) (hb : next + gs.length ≤ base)
    (hout : base + 8 * (i + gs.length) ≤ bound) :
    ∀ p ∈ compileGates base next i gs, Bounded bound p.1 ∧ Bounded bound p.2 := by
  induction gs generalizing next i with
  | nil => intro p hp; cases hp
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := hv
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hw : next < base := by simp only [List.length_cons] at hb; omega
      obtain ⟨hl, hr⟩ := gate_bounded g next base i hg hw p hp
      have hle : base + 8 * i + 8 ≤ bound := by simp only [List.length_cons] at hout; omega
      exact ⟨bounded_mono _ _ _ hle hl, bounded_mono _ _ _ hle hr⟩
    · exact ih (next + 1) (i + 1) hgs
        (by simp only [List.length_cons] at hb; omega)
        (by simp only [List.length_cons] at hout; omega) p hp

theorem correctness : Comparators.CircuitReduction.Correctness := by
  intro c hv ρ
  obtain ⟨hvalid, hl, hr⟩ := hv
  constructor
  · intro heq
    let ν := run c.inputCount c.gates ρ
    obtain ⟨τ, ht, hs⟩ := realize_gates c.gates c.inputCount
      (c.inputCount + c.gates.length) 0 ν hvalid (Nat.le_refl _)
      (run_correct c.gates c.inputCount ρ hvalid)
    have hτ : ∀ j, j < c.inputCount + c.gates.length → τ j = ν j := by
      simpa using ht
    refine ⟨τ, ?_, ?_⟩
    · intro j hj
      rw [hτ j (by omega)]
      exact run_below c.gates c.inputCount ρ j hj
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hs p hp
      · simp only [List.mem_singleton] at hp
        subst p
        change (τ c.leftOutput).val = (τ c.rightOutput).val
        rw [hτ c.leftOutput hl, hτ c.rightOutput hr]
        exact heq
  · rintro ⟨τ, ht, hs⟩
    have hg : GatesCorrect c.inputCount c.gates τ := by
      apply gates_sound c.gates c.inputCount (c.inputCount + c.gates.length) 0 τ
      intro p hp
      exact hs p (List.mem_append_left _ hp)
    have hrun := run_of_correct c.gates c.inputCount τ hg
    have hcon := run_congr c.gates c.inputCount ρ τ hvalid (fun j hj => (ht j hj).symm)
    have hout := hs (.var c.leftOutput, .var c.rightOutput)
      (List.mem_append_right _ (by simp))
    change (run c.inputCount c.gates ρ c.leftOutput).val =
      (run c.inputCount c.gates ρ c.rightOutput).val
    rw [hcon c.leftOutput hl, hcon c.rightOutput hr, hrun]
    exact hout

theorem depthBound : Comparators.CircuitReduction.DepthBound := by
  intro c _ p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact compiled_depth c.gates c.inputCount (c.inputCount + c.gates.length) 0 p hp
  · simp only [List.mem_singleton] at hp
    subst p
    simp [Expr.depth]

theorem variablesBounded : Comparators.CircuitReduction.VariablesBounded := by
  intro c hv p hp
  obtain ⟨hg, hl, hr⟩ := hv
  rcases List.mem_append.mp hp with hp | hp
  · exact compiled_bounded c.gates c.inputCount (c.inputCount + c.gates.length)
      0 (variableBound c) hg (Nat.le_refl _) (by simp [variableBound]; omega) p hp
  · simp only [List.mem_singleton] at hp
    subst p
    change c.leftOutput < variableBound c ∧ c.rightOutput < variableBound c
    simp only [variableBound]
    omega

theorem freshAuxiliaries : Comparators.CircuitReduction.FreshAuxiliaries := by
  intro c i j p q hi hj hp hq
  dsimp [auxiliary, variableBound]
  constructor
  · omega
  constructor
  · omega
  constructor
  · intro h
    constructor <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem circuitReduction : Comparators.CircuitReduction.Target :=
  ⟨correctness, depthBound, variablesBounded, freshAuxiliaries⟩

end LogicLineages.ComputabilityKnowledge.CircuitReductionProof
