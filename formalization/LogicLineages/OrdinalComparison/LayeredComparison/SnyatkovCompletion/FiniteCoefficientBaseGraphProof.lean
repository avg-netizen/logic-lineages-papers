module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsDataProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProgram
open FiniteCoefficientBase

/-- The option operation preserves refusal; no default is substituted for a
failed finite coefficient or a failed child translation. -/
def combine (f : Nat → Nat → Nat) (a b : Option Nat) : Option Nat := do return f (← a) (← b)

theorem combine_primitive (f : Nat → Nat → Nat) (hf : Primrec₂ f) : Primrec₂ (combine f) := by
  let A := Option Nat × Option Nat
  have hm : Primrec₂ (fun p : A => fun x : Nat => p.2.map (fun y => f x y)) :=
    Primrec.option_map (Primrec.snd.comp Primrec.fst)
      (hf.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  apply (Primrec.option_bind Primrec.fst hm).of_eq
  intro p
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

def children (code : Nat) : List Nat :=
  if code % 4 = 0 ∨ code % 4 = 1 then []
  else [(code / 4).unpair.1, (code / 4).unpair.2]

def coefficientAssemble (code : Nat) (xs : List (Option Nat)) : Option Nat :=
  if code % 4 = 0 then some 1
  else if code % 4 = 1 then none
  else if code % 4 = 2 then combine Nat.add (xs.getD 0 none) (xs.getD 1 none)
  else combine (fun a b => 2^a*b) (xs.getD 0 none) (xs.getD 1 none)

theorem decreasing (code child : Nat) (h : child ∈ children code) : child < code := by
  unfold children at h
  split_ifs at h with hz
  · simp at h
  · have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega

theorem coefficient_equation (code : Nat) : Code.coefficient code =
    coefficientAssemble code ((children code).map Code.coefficient) := by
  rw [Code.coefficient]
  unfold coefficientAssemble children combine
  split_ifs <;> simp_all

attribute [local irreducible] Nat.sqrt Nat.unpair

theorem tag : Primrec (fun n : Nat => n % 4) := Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
theorem quotient : Primrec (fun n : Nat => n / 4) := Primrec.nat_div.comp Primrec.id (Primrec.const 4)
theorem left : Primrec (fun n : Nat => (n / 4).unpair.1) := Primrec.fst.comp (Primrec.unpair.comp quotient)
theorem right : Primrec (fun n : Nat => (n / 4).unpair.2) := Primrec.snd.comp (Primrec.unpair.comp quotient)

theorem children_primitive : Primrec children :=
  Primrec.ite ((Primrec.eq.comp tag (Primrec.const 0)).or (Primrec.eq.comp tag (Primrec.const 1)))
    (Primrec.const []) (Primrec.list_cons.comp left (Primrec.list_cons.comp right (Primrec.const [])))

theorem coefficient_assemble_primitive : Primrec₂ coefficientAssemble := by
  let A := Nat × List (Option Nat)
  have h0 : Primrec (fun p : A => p.2.getD 0 none) := (Primrec.list_getD none).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 none) := (Primrec.list_getD none).comp Primrec.snd (Primrec.const 1)
  have hpow : Primrec (fun n : Nat => 2^n) := by
    have hr : Primrec (fun n : Nat => Nat.rec (motive := fun _ => Nat) 1 (fun _ r => 2*r) n) :=
      Primrec.nat_rec' Primrec.id (Primrec.const 1)
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)).to₂
    apply hr.of_eq
    intro n
    induction n <;> simp_all [Nat.pow_succ, Nat.mul_comm]
  have hp : Primrec₂ (fun a b : Nat => 2^a*b) :=
    Primrec.nat_mul.comp (hpow.comp Primrec.fst) Primrec.snd
  exact Primrec.ite (Primrec.eq.comp (tag.comp Primrec.fst) (Primrec.const 0)) (Primrec.const (some 1))
    (Primrec.ite (Primrec.eq.comp (tag.comp Primrec.fst) (Primrec.const 1)) (Primrec.const none)
      (Primrec.ite (Primrec.eq.comp (tag.comp Primrec.fst) (Primrec.const 2))
        ((combine_primitive Nat.add Primrec.nat_add).comp h0 h1)
        ((combine_primitive _ hp).comp h0 h1)))

theorem coefficient_computable : Computable Code.coefficient :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph Nat (Option Nat) children coefficientAssemble id
    children_primitive.to_comp coefficient_assemble_primitive.to_comp Computable.id
    Code.coefficient decreasing coefficient_equation).2

theorem iterate_primitive : Primrec₂ Code.iterate := by
  have hs : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => 4 * p.2.2 + 3) :=
    (SourceBooleanProgramsProof.unary_primitive 4 3).comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_rec' Primrec.fst Primrec.snd hs.to₂

theorem expand_primitive : Primrec₂ Code.expand := by
  have hk : Primrec (fun p : Nat × Nat => 4 * (2*p.1)) :=
    Primrec.nat_mul.comp (Primrec.const 4) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
  have ht : Primrec (fun p : Nat × Nat => 4 * Nat.pair p.2 (4*(2*p.1)) + 2) :=
    (SourceBooleanProgramsProof.binary_primitive 4 2).comp Primrec.snd hk
  exact (SourceBooleanProgramsProof.binary_primitive 4 2).comp
    (iterate_primitive.comp Primrec.fst ht) (Primrec.nat_mul.comp (Primrec.const 4) Primrec.fst)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProgram
