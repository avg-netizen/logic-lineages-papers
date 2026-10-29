module

public import LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthEnvelope
public import LogicLineages.ComputabilityKnowledge.PositiveExpressionProperties
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! External Codex continuation: literal affine numerical envelope only.
No ordinal admissibility or MRDP conclusion is inferred. -/
namespace LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeProof
open PositiveExpression CircuitReduction FiniteDepthEnvelope

private theorem nodes_positive (e : Expr Nat) : 0 < nodeCount e := by
  cases e <;> simp [nodeCount]

private theorem insert_mem (i j : Nat) (xs : List Nat) :
    i ∈ insertVariable j xs ↔ i = j ∨ i ∈ xs := by
  by_cases h : j ∈ xs <;> simp [insertVariable,h] <;> aesop

private theorem distinct_mem (i : Nat) (xs : List Nat) : i ∈ distinctVariables xs ↔ i ∈ xs := by
  induction xs with
  | nil => simp [distinctVariables]
  | cons j xs ih => simpa [distinctVariables,List.foldr_cons,insert_mem] using or_congr Iff.rfl ih

private theorem distinct_nodup (xs : List Nat) : (distinctVariables xs).Nodup := by
  induction xs with
  | nil => simp [distinctVariables]
  | cons j xs ih =>
    change (insertVariable j (distinctVariables xs)).Nodup
    by_cases h : j ∈ distinctVariables xs <;> simp [insertVariable,h,ih]

private theorem sum_depth (xs : List Nat) : (variableSum xs).depth = 0 := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change max 0 (variableSum xs).depth = 0
    simp [ih]

private theorem sum_eval (xs : List Nat) (ρ : Nat → PosNat) :
    (variableSum xs).eval ρ = 1 + (xs.map (fun i => (ρ i).val)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change (ρ i).val + (variableSum xs).eval ρ = 1 + ((ρ i).val + (xs.map (fun i => (ρ i).val)).sum)
    rw [ih]
    omega

private theorem scale_depth (k : Nat) (e : Expr Nat) : (scale k e).depth = e.depth := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scale,Expr.depth,ih]

private theorem scale_eval (k : Nat) (e : Expr Nat) (ρ : Nat → PosNat) :
    (scale k e).eval ρ = (k+1)*e.eval ρ := by
  induction k with
  | zero => simp [scale]
  | succ k ih => simp only [scale,Expr.eval,ih]; nlinarith

theorem literalAffineConstruction : Comparators.FiniteDepthEnvelope.LiteralAffineConstruction := by
  intro e
  refine ⟨nodes_positive e,distinct_nodup _,fun i => distinct_mem i _,sum_depth _,?_,?_,?_⟩
  · simp [bTerm,s0,scale_depth,sum_depth]
  · simp [envelope,bTerm,s0,scale_depth,sum_depth]
  · intro ρ
    exact ⟨sum_eval _ ρ,scale_eval _ _ ρ,scale_eval _ _ ρ,
      PositiveExpressionProperties.eval_positive ρ _,PositiveExpressionProperties.eval_positive ρ _,
      PositiveExpressionProperties.eval_positive ρ _⟩

private theorem bounded_raw (d : Nat) (e : Expr Nat) : Bounded d e ↔ ∀ i ∈ rawVariables e, i < d := by
  induction e with
  | one => simp [Bounded,rawVariables]
  | var i => simp [Bounded,rawVariables]
  | add a b ha hb | emul a b ha hb => simp only [Bounded,rawVariables,ha,hb,List.mem_append]; aesop

private theorem bounded_sum (d : Nat) (xs : List Nat) : Bounded d (variableSum xs) ↔ ∀ i ∈ xs, i < d := by
  induction xs with
  | nil => simp [Bounded,variableSum]
  | cons i xs ih =>
    change (i < d ∧ Bounded d (variableSum xs)) ↔ ∀ j ∈ i::xs, j < d
    simp [ih]

private theorem bounded_scale (d k : Nat) (e : Expr Nat) : Bounded d (scale k e) ↔ Bounded d e := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scale,Bounded,ih]

theorem sameVariables : Comparators.FiniteDepthEnvelope.SameVariables := by
  intro d e
  change Bounded d (scale 4 (scale (nodeCount e) (variableSum (variableList e)))) ↔ Bounded d e
  rw [bounded_scale,bounded_scale,bounded_sum,bounded_raw]
  simp only [variableList,distinct_mem]

/-- Flattening addition contributes at most one envelope atom per source node. -/
private theorem flat_bound (k L s A : Nat) (ρ : Nat → PosNat)
    (hs : s ≤ A) (h1 : 1 ≤ A)
    (hE : ∀ a b : Expr Nat, nodeCount (.emul a b) ≤ L → (Expr.emul a b).depth ≤ k →
      (∀ i ∈ rawVariables (.emul a b), (ρ i).val ≤ s) → (Expr.emul a b).eval ρ ≤ A)
    (e : Expr Nat) (hn : nodeCount e ≤ L) (hd : e.depth ≤ k)
    (hv : ∀ i ∈ rawVariables e, (ρ i).val ≤ s) : e.eval ρ ≤ nodeCount e * A := by
  induction e with
  | one => simpa [Expr.eval,nodeCount] using h1
  | var i => simpa [Expr.eval,nodeCount] using (hv i (by simp [rawVariables])).trans hs
  | add a b ha hb =>
    have hna : nodeCount a ≤ L := by simp only [nodeCount] at hn; omega
    have hnb : nodeCount b ≤ L := by simp only [nodeCount] at hn; omega
    have hda : a.depth ≤ k := by simp only [Expr.depth] at hd; omega
    have hdb : b.depth ≤ k := by simp only [Expr.depth] at hd; omega
    have hA := ha hna hda (fun i hi => hv i (by simp [rawVariables,hi]))
    have hB := hb hnb hdb (fun i hi => hv i (by simp [rawVariables,hi]))
    simp only [Expr.eval,nodeCount]
    nlinarith
  | emul a b ha hb =>
    have h := hE a b hn hd hv
    have hp := nodes_positive (Expr.emul a b)
    nlinarith

private theorem zero_bound (L s : Nat) (ρ : Nat → PosNat) (hs : 1 ≤ s)
    (e : Expr Nat) (hn : nodeCount e ≤ L) (hd : e.depth ≤ 0)
    (hv : ∀ i ∈ rawVariables e, (ρ i).val ≤ s) : e.eval ρ ≤ nodeCount e*s := by
  apply flat_bound 0 L s s ρ le_rfl hs _ e hn hd hv
  intro a b _ h _
  simp only [Expr.depth] at h
  omega

private theorem one_bound (L s b : Nat) (ρ : Nat → PosNat) (hs : 1 ≤ s)
    (hsb : s ≤ b) (hLs : L*s ≤ b)
    (e : Expr Nat) (hn : nodeCount e ≤ L) (hd : e.depth ≤ 1)
    (hv : ∀ i ∈ rawVariables e, (ρ i).val ≤ s) : e.eval ρ ≤ nodeCount e*(b*2^b) := by
  have hp : 1 ≤ 2^b := Nat.one_le_two_pow
  apply flat_bound 1 L s (b*2^b) ρ (by nlinarith) (by nlinarith) _ e hn hd hv
  intro a c hn hd hv
  have hna : nodeCount a ≤ L := by simp only [nodeCount] at hn; omega
  have hnc : nodeCount c ≤ L := by simp only [nodeCount] at hn; omega
  have hda : a.depth ≤ 0 := by simp only [Expr.depth] at hd; omega
  have hdc : c.depth ≤ 0 := by simp only [Expr.depth] at hd; omega
  have hA := zero_bound L s ρ hs a hna hda (fun i hi => hv i (by simp [rawVariables,hi]))
  have hC := zero_bound L s ρ hs c hnc hdc (fun i hi => hv i (by simp [rawVariables,hi]))
  have ha : a.eval ρ ≤ b := hA.trans ((Nat.mul_le_mul_right s hna).trans hLs)
  have hc : c.eval ρ ≤ b := hC.trans ((Nat.mul_le_mul_right s hnc).trans hLs)
  exact (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) ha) hc).trans_eq (Nat.mul_comm _ _)

private theorem le_pow_two (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; have := Nat.one_le_two_pow (n := n); omega

private theorem numeric_envelope (L s b : Nat) (ρ : Nat → PosNat)
    (hs : 1 ≤ s) (hLb : L ≤ b) (hsb : s ≤ b) (hLs : L*s ≤ b)
    (e : Expr Nat) (hn : nodeCount e ≤ L) (hd : e.depth ≤ 2)
    (hv : ∀ i ∈ rawVariables e, (ρ i).val ≤ s) : e.eval ρ ≤ 2^(2^(5*b)) := by
  have hb : 1 ≤ b := hs.trans hsb
  have hbp : b ≤ 2^b := le_pow_two b
  have hLp : L ≤ 2^b := hLb.trans hbp
  have hprod : L*(b*2^b) ≤ 2^(3*b) := by
    calc
      L*(b*2^b) ≤ 2^b*(2^b*2^b) := Nat.mul_le_mul hLp (Nat.mul_le_mul_right _ hbp)
      _ = 2^(3*b) := by rw [show 3*b = b+(b+b) by omega,pow_add,pow_add]
  have hsmall (a : Expr Nat) (ha : nodeCount a ≤ L) (hda : a.depth ≤ 1)
      (hva : ∀ i ∈ rawVariables a, (ρ i).val ≤ s) : a.eval ρ ≤ 2^(3*b) :=
    (one_bound L s b ρ hs hsb hLs a ha hda hva).trans
      ((Nat.mul_le_mul_right _ ha).trans hprod)
  let A := 2^(2^(3*b)+3*b)
  have hA : e.eval ρ ≤ nodeCount e*A := by
    apply flat_bound 2 L s A ρ
      (hsb.trans (hbp.trans (Nat.pow_le_pow_right (by decide) (by omega))))
      Nat.one_le_two_pow _ e hn hd hv
    intro a c hn hd hv
    have hna : nodeCount a ≤ L := by simp only [nodeCount] at hn; omega
    have hnc : nodeCount c ≤ L := by simp only [nodeCount] at hn; omega
    have hda : a.depth ≤ 1 := by simp only [Expr.depth] at hd; omega
    have hdc : c.depth ≤ 1 := by simp only [Expr.depth] at hd; omega
    have ha := hsmall a hna hda (fun i hi => hv i (by simp [rawVariables,hi]))
    have hc := hsmall c hnc hdc (fun i hi => hv i (by simp [rawVariables,hi]))
    calc
      (.emul a c : Expr Nat).eval ρ ≤ 2^(2^(3*b))*2^(3*b) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) ha) hc
      _ = A := (pow_add _ _ _).symm
  have hfour : 4*b ≤ 2^(3*b) := by
    calc
      4*b ≤ 4*2^b := Nat.mul_le_mul_left 4 hbp
      _ = 2^(b+2) := by rw [pow_add]; simp [Nat.mul_comm]
      _ ≤ 2^(3*b) := Nat.pow_le_pow_right (by decide) (by omega)
  have hexp : 2^(3*b)+4*b ≤ 2^(5*b) := by
    calc
      2^(3*b)+4*b ≤ 2^(3*b)*2 := by omega
      _ = 2^(3*b+1) := (pow_succ _ _).symm
      _ ≤ 2^(5*b) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    e.eval ρ ≤ L*A := hA.trans (Nat.mul_le_mul_right A hn)
    _ ≤ 2^b*A := Nat.mul_le_mul_right A hLp
    _ = 2^(2^(3*b)+4*b) := by dsimp [A]; rw [←pow_add]; congr 1; omega
    _ ≤ 2^(2^(5*b)) := Nat.pow_le_pow_right (by decide) hexp

theorem depthTwoBound : Comparators.FiniteDepthEnvelope.DepthTwoBound := by
  intro e hd ρ
  let L := nodeCount e
  let s := (s0 e).eval ρ
  let b := (bTerm e).eval ρ
  have hs : 1 ≤ s := PositiveExpressionProperties.eval_positive ρ (s0 e)
  have hb : b = (L+1)*s := scale_eval _ _ ρ
  have hv : ∀ i ∈ rawVariables e, (ρ i).val ≤ s := by
    intro i hi
    have hi' : i ∈ variableList e := (distinct_mem i _).mpr hi
    have hm : (ρ i).val ∈ ((variableList e).map (fun j => (ρ j).val)) := List.mem_map.mpr ⟨i,hi',rfl⟩
    have member_sum : ∀ (xs : List Nat) (a : Nat), a ∈ xs → a ≤ xs.sum := by
      intro xs
      induction xs with
      | nil => intro a ha; simp at ha
      | cons b xs ih =>
        intro a ha
        simp only [List.mem_cons] at ha
        simp only [List.sum_cons]
        rcases ha with h | h
        · omega
        · exact (ih a h).trans (Nat.le_add_left _ _)
    have hsum := member_sum _ _ hm
    dsimp [s]
    rw [show (s0 e).eval ρ = 1+((variableList e).map (fun j => (ρ j).val)).sum from sum_eval _ ρ]
    omega
  have h := numeric_envelope L s b ρ hs (by nlinarith [hb]) (by nlinarith [hb])
    (by nlinarith [hb]) e le_rfl hd hv
  simpa only [envelope,scale_eval] using h

theorem finiteDepthEnvelope : Comparators.FiniteDepthEnvelope.Target :=
  ⟨literalAffineConstruction,sameVariables,depthTwoBound⟩
end LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelopeProof
