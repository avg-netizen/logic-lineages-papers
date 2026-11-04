module
public import LogicLineages.OrdinalComparison.ParametricPairMachineCodeTargets
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode.Proof
open ParametricFinitePairCollapse ParametricPairWorklist

private theorem filterPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).filter (g a)) := by
  have hc : Primrec (fun p : A × B => bif g p.1 p.2 then some p.2 else none) :=
    Primrec.cond hg (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  apply (Primrec.listFilterMap hf hc.to₂).of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b bs ih => cases hb : g a b <;> simp [hb, ih]

private theorem normPrimitive : Primrec pairNorm :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) Primrec.snd

private theorem belowPrimitive : PrimrecRel Below :=
  (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).or
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).and
      (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))

private theorem childrenPrimitive :
    Primrec (fun p : (Nat × Nat) × Nat => childrenBudget p.1 p.2) := by
  have hrow : Primrec (fun z : ((Nat × Nat) × Nat) × Nat =>
      (List.range (z.1.2 + 1)).map (fun b => (z.2,b))) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)))
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  have hrect : Primrec (fun p : (Nat × Nat) × Nat =>
      (List.range (p.1.1+1)).flatMap (fun a =>
        (List.range (p.2+1)).map (fun b => (a,b)))) :=
    Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))) hrow.to₂
  have htest : PrimrecPred (fun z : ((Nat × Nat) × Nat) × (Nat × Nat) =>
      Below z.2 z.1.1 ∧ pairNorm z.2 ≤ z.1.2) :=
    (belowPrimitive.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
      (Primrec.nat_le.comp (normPrimitive.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
  exact filterPrimitive hrect htest.decide.to₂

private theorem combinePrimitive : Primrec combine :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem queryPrimitive : Primrec query := by
  have ht : Primrec (fun t : Task => (Sum.casesOn t pairNorm (fun _ => 0) : Nat)) :=
    Primrec.sumCasesOn Primrec.id (normPrimitive.comp Primrec.snd).to₂
      (Primrec.const 0).to₂
  have h := Primrec.list_casesOn (Primrec.fst (α := List Task) (β := List Nat))
    (Primrec.const 0) (ht.comp (Primrec.fst.comp Primrec.snd)).to₂
  apply h.of_eq
  rintro ⟨ts,vs⟩
  cases ts with
  | nil => rfl
  | cons t ts => cases t <;> rfl

private abbrev Frame := Nat × List Task × List Nat
private def process (f : Frame) (t : Task) : State :=
  Sum.casesOn t
    (fun p => let qs := childrenBudget p f.1
              (qs.map Sum.inl ++ Sum.inr qs.length :: f.2.1, f.2.2))
    (fun k => if k ≤ f.2.2.length then
      (f.2.1, combine (f.2.2.take k) :: f.2.2.drop k)
      else (Sum.inr k :: f.2.1, f.2.2))

private theorem processPrimitive : Primrec₂ process := by
  have hl : Primrec (fun z : (Frame × Task) × (Nat × Nat) =>
      let qs := childrenBudget z.2 z.1.1.1
      (qs.map Sum.inl ++ Sum.inr qs.length :: z.1.1.2.1, z.1.1.2.2)) := by
    have hq : Primrec (fun z : (Frame × Task) × (Nat × Nat) =>
        childrenBudget z.2 z.1.1.1) :=
      childrenPrimitive.comp (Primrec.snd.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hts : Primrec (fun z : (Frame × Task) × (Nat × Nat) => z.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hvs : Primrec (fun z : (Frame × Task) × (Nat × Nat) => z.1.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    exact (Primrec.list_append.comp
      (Primrec.list_map hq (Primrec.sumInl.comp Primrec.snd).to₂)
      (Primrec.list_cons.comp (Primrec.sumInr.comp (Primrec.list_length.comp hq)) hts)).pair hvs
  have hr : Primrec (fun z : (Frame × Task) × Nat =>
      if z.2 ≤ z.1.1.2.2.length then
        (z.1.1.2.1, combine (z.1.1.2.2.take z.2) :: z.1.1.2.2.drop z.2)
      else (Sum.inr z.2 :: z.1.1.2.1, z.1.1.2.2)) := by
    have hts : Primrec (fun z : (Frame × Task) × Nat => z.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hvs : Primrec (fun z : (Frame × Task) × Nat => z.1.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    exact Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.list_length.comp hvs))
      (hts.pair (Primrec.list_cons.comp
        (combinePrimitive.comp (Primrec.list_take.comp Primrec.snd hvs))
        (Primrec.list_drop.comp Primrec.snd hvs)))
      ((Primrec.list_cons.comp (Primrec.sumInr.comp Primrec.snd) hts).pair hvs)
  exact (Primrec.sumCasesOn Primrec.snd hl.to₂ hr.to₂).to₂

private theorem stepPrimitive : Primrec (fun p : Nat × State => stepBudget p.1 p.2) := by
  have hc : Primrec (fun z : (Nat × State) × (Task × List Task) =>
      process (z.1.1, z.2.2, z.1.2.2) z.2.1) :=
    processPrimitive.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.fst.comp Primrec.snd)
  apply (Primrec.list_casesOn (Primrec.fst.comp Primrec.snd) Primrec.snd hc.to₂).of_eq
  rintro ⟨B,ts,vs⟩
  cases ts with
  | nil => rfl
  | cons t ts => cases t <;> rfl

private theorem resultPrimitive : Primrec result := by
  have ht : PrimrecPred (fun s : State => s.1 = [] ∧ s.2.length = 1) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const [])).and
      (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1))
  have h := Primrec.ite ht (Primrec.list_head?.comp Primrec.snd) (Primrec.const none)
  apply h.of_eq
  rintro ⟨ts,vs⟩
  cases ts with
  | cons t ts => simp [result]
  | nil =>
    cases vs with
    | nil => simp [result]
    | cons v vs => cases vs <;> simp [result]

theorem kernelPrimitiveRecursive : Targets.KernelPrimitiveRecursive :=
  ⟨childrenPrimitive, queryPrimitive, stepPrimitive, resultPrimitive⟩
end LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode.Proof
