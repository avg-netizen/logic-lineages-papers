module

public import LogicLineages.ComputabilityKnowledge.Comparators.PolynomialCircuit
public import Mathlib.Tactic.Ring

@[expose] public section

/-! External Codex continuation proof for the frozen positive-polynomial circuit
front end. Coverage is mathematical representation, not an MRDP supplier. -/
namespace LogicLineages.ComputabilityKnowledge.PolynomialCircuitProof

open PositiveExpression CircuitReduction PolynomialCircuit

private theorem product_eval (vs : List Nat) (ρ : Nat → PosNat) :
    MvPolynomial.eval (fun i => ((ρ i).val : Int)) (variableProduct vs) = (productValue ρ vs : Int) := by
  induction vs with
  | nil => simp [variableProduct,productValue]
  | cons i vs ih => simp [variableProduct,productValue,ih]

private theorem coeff_split (z : Int) : (z.toNat : Int) - ((-z).toNat : Int) = z := by omega

private theorem terms_eval (ms : Monomials) (ρ : Nat → PosNat) :
    MvPolynomial.eval (fun i => ((ρ i).val : Int)) (interpretTerms ms) =
      (positiveTotal ρ ms : Int) - (negativeTotal ρ ms : Int) := by
  induction ms with
  | nil => simp [interpretTerms,positiveTotal,negativeTotal]
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    simp only [interpretTerms,map_add,map_mul,MvPolynomial.eval_C,product_eval,ih,
      positiveTotal,negativeTotal,Nat.cast_add,Nat.cast_mul]
    conv_lhs => rw [← coeff_split z]
    ring

theorem interpretationCorrect : Comparators.PolynomialCircuit.InterpretationCorrect :=
  fun p ρ => terms_eval p.monomials ρ

private theorem run_append (as bs : List Gate) (n : Nat) (ρ : Nat → PosNat) :
    run n (as ++ bs) ρ = run (n + as.length) bs (run n as ρ) := by
  induction as generalizing n ρ with
  | nil => simp [run]
  | cons g gs ih => simp [run,ih,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

private theorem valid_append (as bs : List Gate) (n : Nat) :
    ValidFrom n (as ++ bs) ↔ ValidFrom n as ∧ ValidFrom (n + as.length) bs := by
  induction as generalizing n with
  | nil => simp [ValidFrom]
  | cons g gs ih => simp [ValidFrom,ih,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,and_assoc]

private theorem run_below (gs : List Gate) (n : Nat) (ρ : Nat → PosNat)
    (j : Nat) (hj : j < n) : run n gs ρ j = ρ j := by
  induction gs generalizing n ρ with
  | nil => rfl
  | cons g gs ih =>
    rw [run,ih (n+1) (assign ρ n (g.eval ρ)) (by omega)]
    simp [assign,show j ≠ n by omega]

private theorem run_last_at (gs : List Gate) (g : Gate) (n : Nat) (ρ : Nat → PosNat) :
    run n (gs ++ [g]) ρ (n + gs.length) = g.eval (run n gs ρ) := by
  rw [run_append]
  simp [run,assign]

private theorem run_last_below (gs : List Gate) (g : Gate) (n : Nat) (ρ : Nat → PosNat)
    (j : Nat) (hj : j < n + gs.length) : run n (gs ++ [g]) ρ j = run n gs ρ j := by
  rw [run_append]
  exact run_below [g] _ _ j hj

private theorem product_congr (vs : List Nat) (ρ τ : Nat → PosNat)
    (h : ∀ i ∈ vs, ρ i = τ i) : productValue ρ vs = productValue τ vs := by
  induction vs with
  | nil => rfl
  | cons i vs ih =>
    simp only [productValue,h i (by simp)]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

private theorem multiply_length (vs : List Nat) (acc : Nat) :
    (multiplyInputs acc vs).length = vs.length := by
  induction vs generalizing acc with
  | nil => rfl
  | cons i vs ih => simp [multiplyInputs,ih]

private theorem monomial_length (start k : Nat) (vs : List Nat) :
    (monomialGates start k vs).length = vs.length + 1 := by
  simp [monomialGates,multiply_length,Nat.add_comm]

private theorem multiply_valid (vs : List Nat) (acc : Nat)
    (hv : ∀ i ∈ vs, i < acc) : ValidFrom (acc+1) (multiplyInputs acc vs) := by
  induction vs generalizing acc with
  | nil => trivial
  | cons i vs ih =>
    refine ⟨⟨by omega,by have := hv i (by simp); omega⟩,?_⟩
    exact ih (acc+1) (fun j hj => by have := hv j (List.mem_cons_of_mem _ hj); omega)

private theorem monomial_valid (start k : Nat) (vs : List Nat)
    (hv : ∀ i ∈ vs, i < start) : ValidFrom start (monomialGates start k vs) :=
  ⟨trivial,multiply_valid vs start hv⟩

private theorem multiply_value (vs : List Nat) (acc : Nat) (ρ : Nat → PosNat)
    (hv : ∀ i ∈ vs, i < acc) :
    (run (acc+1) (multiplyInputs acc vs) ρ (acc+vs.length)).val =
      (ρ acc).val * productValue ρ vs := by
  induction vs generalizing acc ρ with
  | nil => simp [multiplyInputs,run,productValue]
  | cons i vs ih =>
    let η := assign ρ (acc+1) ((Gate.mul acc i).eval ρ)
    have hp : productValue η vs = productValue ρ vs := by
      apply product_congr
      intro j hj
      have hj' := hv j (List.mem_cons_of_mem _ hj)
      simp [η,assign,show j ≠ acc+1 by omega]
    have hi := ih (acc+1) η (fun j hj => by have := hv j (List.mem_cons_of_mem _ hj); omega)
    change (run ((acc+1)+1) (multiplyInputs (acc+1) vs) η (acc+(i::vs).length)).val = _
    rw [show acc+(i::vs).length = (acc+1)+vs.length by simp; omega,hi,hp]
    simp [η,assign,Gate.eval,productValue,Nat.mul_assoc]

private theorem monomial_value (start k : Nat) (vs : List Nat) (ρ : Nat → PosNat)
    (hv : ∀ i ∈ vs, i < start) :
    (run start (monomialGates start k vs) ρ (start+vs.length)).val =
      (k+1) * productValue ρ vs := by
  let η := assign ρ start ((Gate.constant k).eval ρ)
  have hp : productValue η vs = productValue ρ vs := by
    apply product_congr
    intro j hj
    simp [η,assign,show j ≠ start by have := hv j hj; omega]
  change (run (start+1) (multiplyInputs start vs) η (start+vs.length)).val = _
  rw [multiply_value vs start η hv,hp]
  simp [η,assign,Gate.eval]

private def Good (n : Nat) (s : State) : Prop :=
  ValidFrom n s.gates ∧ 2 ≤ s.gates.length ∧
    n ≤ s.left ∧ s.left < n+s.gates.length ∧ n ≤ s.right ∧ s.right < n+s.gates.length

private theorem initial_good (n : Nat) : Good n (initial n) := by
  simp [Good,initial,ValidFrom,Gate.ValidAt]

private theorem emit_good (n : Nat) (pos : Bool) (s : State) (k : Nat) (vs : List Nat)
    (hs : Good n s) (hv : ∀ i ∈ vs, i < n) : Good n (emit n pos s k vs) := by
  obtain ⟨hsvalid,hlen,hl0,hl,hr0,hr⟩ := hs
  have hv' : ∀ i ∈ vs, i < n+s.gates.length := fun i hi => by have := hv i hi; omega
  have hterm := monomial_valid (n+s.gates.length) k vs hv'
  have hvalid (old : Nat) (hold : old < n+s.gates.length) :
      ValidFrom n (s.gates ++ monomialGates (n+s.gates.length) k vs ++
        [.add old (n+s.gates.length+vs.length)]) := by
    apply (valid_append _ _ n).mpr
    constructor
    · exact (valid_append _ _ n).mpr ⟨hsvalid,hterm⟩
    · simp only [List.length_append,monomial_length,ValidFrom,Gate.ValidAt]
      exact ⟨⟨by omega,by omega⟩,trivial⟩
  cases pos <;> dsimp [emit,Good]
  · refine ⟨hvalid s.right hr,?_,hl0,?_,?_,?_⟩ <;>
      (try simp only [List.length_append,List.length_singleton,monomial_length]) <;> omega
  · refine ⟨hvalid s.left hl,?_,?_,?_,hr0,?_⟩ <;>
      (try simp only [List.length_append,List.length_singleton,monomial_length]) <;> omega

private theorem emit_values (n : Nat) (pos : Bool) (s : State) (k : Nat) (vs : List Nat)
    (hs : Good n s) (hv : ∀ i ∈ vs, i < n) (ρ : Nat → PosNat) :
    let t := emit n pos s k vs
    (run n t.gates ρ t.left).val = (run n s.gates ρ s.left).val +
      (if pos then (k+1)*productValue ρ vs else 0) ∧
    (run n t.gates ρ t.right).val = (run n s.gates ρ s.right).val +
      (if pos then 0 else (k+1)*productValue ρ vs) := by
  obtain ⟨_,_,_,hl,_,hr⟩ := hs
  let start := n+s.gates.length
  let gs := s.gates ++ monomialGates start k vs
  let w := start+vs.length+1
  have hw : n+gs.length = w := by simp [gs,w,start,monomial_length]; omega
  have hp : productValue (run n s.gates ρ) vs = productValue ρ vs :=
    product_congr vs _ _ (fun i hi => run_below s.gates n ρ i (hv i hi))
  have hvalue : (run n gs ρ (start+vs.length)).val = (k+1)*productValue ρ vs := by
    rw [show gs = s.gates ++ monomialGates start k vs from rfl,run_append]
    rw [monomial_value start k vs _ (fun i hi => by have := hv i hi; dsimp [start]; omega),hp]
  have hold (j : Nat) (hj : j < start) : run n gs ρ j = run n s.gates ρ j := by
    rw [show gs = s.gates ++ monomialGates start k vs from rfl,run_append]
    exact run_below _ start _ j hj
  have hadd (j : Nat) (hj : j < start) :
      (run n (gs ++ [.add j (start+vs.length)]) ρ w).val =
        (run n s.gates ρ j).val + (k+1)*productValue ρ vs := by
    rw [←hw,run_last_at]
    change (run n gs ρ j).val + (run n gs ρ (start+vs.length)).val = _
    rw [hold j hj,hvalue]
  have hkeep (j old : Nat) (hj : j < start) :
      run n (gs ++ [.add old (start+vs.length)]) ρ j = run n s.gates ρ j := by
    rw [run_last_below _ _ _ _ j (by rw [hw]; dsimp [w]; omega),hold j hj]
  cases pos
  · change (run n (gs ++ [.add s.right (start+vs.length)]) ρ s.left).val = _ ∧
      (run n (gs ++ [.add s.right (start+vs.length)]) ρ w).val = _
    simp only [Bool.false_eq_true,if_false,Nat.add_zero]
    exact ⟨congrArg Subtype.val (hkeep s.left s.right hl),hadd s.right hr⟩
  · change (run n (gs ++ [.add s.left (start+vs.length)]) ρ w).val = _ ∧
      (run n (gs ++ [.add s.left (start+vs.length)]) ρ s.right).val = _
    simp only [if_true,Nat.add_zero]
    exact ⟨hadd s.left hl,congrArg Subtype.val (hkeep s.right s.left hr)⟩

private theorem fold_correct (ms : Monomials) (n : Nat) (s : State) (ρ : Nat → PosNat)
    (hs : Good n s) (hv : ∀ m ∈ ms, ∀ i ∈ m.2, i < n) :
    let t := ms.foldl (step n) s
    Good n t ∧
    (run n t.gates ρ t.left).val = (run n s.gates ρ s.left).val + positiveTotal ρ ms ∧
    (run n t.gates ρ t.right).val = (run n s.gates ρ s.right).val + negativeTotal ρ ms := by
  induction ms generalizing s with
  | nil => simpa [positiveTotal,negativeTotal] using hs
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    have hm := hv (z,vs) (by simp)
    have htail := fun m hmem => hv m (List.mem_cons_of_mem _ hmem)
    cases z with
    | ofNat k =>
      cases k with
      | zero => simpa [step,positiveTotal,negativeTotal] using ih s hs htail
      | succ k =>
        have hgood := emit_good n true s k vs hs hm
        have hvals := emit_values n true s k vs hs hm ρ
        have hrec := ih (emit n true s k vs) hgood htail
        dsimp only [List.foldl_cons,step]
        refine ⟨hrec.1,?_,?_⟩
        · rw [hrec.2.1,hvals.1]
          simp [positiveTotal,Nat.add_assoc]
        · rw [hrec.2.2,hvals.2]
          simp [negativeTotal]
    | negSucc k =>
      have hgood := emit_good n false s k vs hs hm
      have hvals := emit_values n false s k vs hs hm ρ
      have hrec := ih (emit n false s k vs) hgood htail
      dsimp only [List.foldl_cons,step]
      refine ⟨hrec.1,?_,?_⟩
      · rw [hrec.2.1,hvals.1]
        simp [positiveTotal]
      · rw [hrec.2.2,hvals.2]
        simp [negativeTotal,Nat.add_assoc]

private theorem build_good (p : Code) (hp : p.WellFormed) : Good p.inputCount (build p) :=
  (fold_correct p.monomials p.inputCount (initial p.inputCount)
    (fun _ => ⟨1,Nat.zero_lt_one⟩) (initial_good _) hp).1

theorem compiledWellFormed : Comparators.PolynomialCircuit.CompiledWellFormed := by
  intro p hp
  have h := build_good p hp
  exact ⟨rfl,h.1,h.2.2.2.1,h.2.2.2.2.2⟩

theorem outputValues : Comparators.PolynomialCircuit.OutputValues := by
  intro p hp ρ
  have h := (fold_correct p.monomials p.inputCount (initial p.inputCount) ρ (initial_good _) hp).2
  have hl : (run p.inputCount (initial p.inputCount).gates ρ (initial p.inputCount).left).val = 1 := by
    simp only [initial,run,Gate.eval,assign,ite_true] <;> split_ifs <;> rfl
  have hr : (run p.inputCount (initial p.inputCount).gates ρ (initial p.inputCount).right).val = 1 := by
    simp only [initial,run,Gate.eval,assign,ite_true] <;> split_ifs <;> rfl
  rw [hl,hr] at h
  exact h

theorem inputsPreserved : Comparators.PolynomialCircuit.InputsPreserved := by
  intro p _ ρ i hi
  exact run_below (PolynomialCircuit.compile p).gates p.inputCount ρ i hi

theorem freshOutputs : Comparators.PolynomialCircuit.FreshOutputs := by
  intro p hp
  have h := build_good p hp
  exact ⟨h.2.1,h.2.2.1,h.2.2.2.2.1⟩

theorem zeroIff : Comparators.PolynomialCircuit.ZeroIff := by
  intro p hp ρ
  have h := outputValues p hp ρ
  rw [interpretationCorrect p ρ]
  change _ ↔ (run (PolynomialCircuit.compile p).inputCount (PolynomialCircuit.compile p).gates ρ
    (PolynomialCircuit.compile p).leftOutput).val =
      (run (PolynomialCircuit.compile p).inputCount (PolynomialCircuit.compile p).gates ρ
        (PolynomialCircuit.compile p).rightOutput).val
  rw [h.1,h.2]
  omega

private theorem interpret_append (as bs : Monomials) :
    interpretTerms (as ++ bs) = interpretTerms as + interpretTerms bs := by
  induction as with
  | nil => simp [interpretTerms]
  | cons a as ih => simp [interpretTerms,ih,add_assoc]

private theorem product_append_var (vs : List Nat) (i : Nat) :
    variableProduct (vs ++ [i]) = variableProduct vs * MvPolynomial.X i := by
  induction vs with
  | nil => simp [variableProduct]
  | cons j vs ih => simp [variableProduct,ih,mul_assoc]

private theorem interpret_mul_var (ms : Monomials) (i : Nat) :
    interpretTerms (ms.map (fun m => (m.1,m.2 ++ [i]))) = interpretTerms ms * MvPolynomial.X i := by
  induction ms with
  | nil => simp [interpretTerms]
  | cons m ms ih => simp [interpretTerms,product_append_var,ih,add_mul,mul_assoc]

theorem coverage : Comparators.PolynomialCircuit.Coverage := by
  intro n P
  induction P using MvPolynomial.induction_on with
  | C z =>
    refine ⟨⟨n,[(z,[])]⟩,rfl,?_,?_⟩
    · simp [Code.WellFormed]
    · simp [interpret,interpretTerms,variableProduct]
  | add P Q hP hQ =>
    obtain ⟨p,hpn,hp,hPe⟩ := hP
    obtain ⟨q,hqn,hq,hQe⟩ := hQ
    refine ⟨⟨n,p.monomials ++ q.monomials⟩,rfl,?_,?_⟩
    · intro m hm i hi
      rcases List.mem_append.mp hm with hm | hm
      · simpa [hpn] using hp m hm i hi
      · simpa [hqn] using hq m hm i hi
    · simpa [interpret,interpret_append] using congrArg₂ (· + ·) hPe hQe
  | mul_X P i hP =>
    obtain ⟨p,hpn,hp,hPe⟩ := hP
    refine ⟨⟨n,p.monomials.map (fun m => (m.1,m.2 ++ [i.val]))⟩,rfl,?_,?_⟩
    · intro m hm j hj
      obtain ⟨m',hm',rfl⟩ := List.mem_map.mp hm
      rcases List.mem_append.mp hj with hj | hj
      · simpa [hpn] using hp m' hm' j hj
      · simp only [List.mem_singleton] at hj
        subst j
        exact i.isLt
    · simp only [interpret,interpret_mul_var,map_mul,MvPolynomial.rename_X]
      exact congrArg (fun q => q * MvPolynomial.X i.val) hPe

theorem polynomialCircuit : Comparators.PolynomialCircuit.Target :=
  ⟨interpretationCorrect,compiledWellFormed,outputValues,inputsPreserved,freshOutputs,zeroIff,coverage⟩

end LogicLineages.ComputabilityKnowledge.PolynomialCircuitProof
