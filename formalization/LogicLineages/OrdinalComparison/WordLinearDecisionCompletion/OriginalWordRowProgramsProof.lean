module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordListProgramsProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.CodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof.Numeric
open PolynomialGraphCompletion LayeredComparison LayeredComparison.SnyatkovCompletion
attribute [local irreducible] Nat.sqrt Nat.unpair word wordDomain letter letterDomain OriginalScheduled.sourceCount

theorem listFilterPrimitive {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → β → Bool} (hp : Primrec₂ p) :
    Primrec₂ (fun (a : α) (xs : List β) => xs.filter (p a)) := by
  let A := α × List β
  have hs : Primrec (fun q : A × (β × List β) =>
      bif p q.1.1 q.2.1 then q.2.1 :: q.2.2 else q.2.2) :=
    Primrec.cond
      (hp.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun q : A => q.2.foldr
      (fun b s => bif p q.1 b then b :: s else s) []) :=
    Primrec.list_foldr Primrec.snd (Primrec.const []) hs.to₂
  apply hf.to₂.of_eq
  intro a xs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.foldr_cons, List.filter_cons, ih]
    cases h : p a b <;> simp [h]

theorem integerSumPrimitive : Primrec (fun xs : List Int => xs.sum) := by
  have hs : Primrec (fun p : List Int × (Int × Int) => p.2.1 + p.2.2) :=
    IntegerAlgorithms.Proof.add_primitive.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Int => xs.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const (0 : Int)) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, List.sum_cons, ih]

abbrev PrefixInput := Nat × Nat × Row
abbrev WordItem := Int × Token

theorem specializeRowComputable :
    Computable (fun p : PrefixInput => specializeRow p.1 p.2.1 p.2.2) := by
  have hx : Computable (fun p : PrefixInput × WordItem => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hn : Computable (fun p : PrefixInput × WordItem => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hc : Computable (fun p : PrefixInput × WordItem => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hname : Computable (fun p : PrefixInput × WordItem => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hw : Computable (fun p : PrefixInput × WordItem => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hv : Computable (fun p : PrefixInput × WordItem => (word p.2.2.2 p.1.2.1 : Int)) :=
    IntegerAlgorithms.Proof.ofNat_primitive.to_comp.comp (wordPrograms.1.comp (hw.pair hn))
  have heq : Computable (fun p : PrefixInput × WordItem => decide (p.2.2.1 = p.1.1)) :=
    Primrec.eq.decide.to_comp.comp hname hx
  have hterm : Computable (fun p : PrefixInput × WordItem =>
      if p.2.2.1 = p.1.1 then p.2.1 * (word p.2.2.2 p.1.2.1 : Int) else 0) :=
    computableIf heq (IntegerAlgorithms.Proof.mul_primitive.to_comp.comp hc hv)
      (Computable.const (0 : Int))
  have hentries : Primrec (fun p : PrefixInput => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hm : Computable (fun p : PrefixInput => p.2.2.2.map (fun b =>
      if b.2.1 = p.1 then b.1 * (word b.2.2 p.2.1 : Int) else 0)) :=
    computableListMap (g := fun (p : PrefixInput) (b : WordItem) =>
      if b.2.1 = p.1 then b.1 * (word b.2.2 p.2.1 : Int) else 0) hentries.to_comp hterm.to₂
  have hz : Computable (fun p : PrefixInput => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hconstant : Computable (fun p : PrefixInput => p.2.2.1 +
      (p.2.2.2.map (fun b => if b.2.1 = p.1 then b.1 * (word b.2.2 p.2.1 : Int) else 0)).sum) :=
    IntegerAlgorithms.Proof.add_primitive.to_comp.comp hz (integerSumPrimitive.to_comp.comp hm)
  have hkeep : Primrec (fun p : PrefixInput × WordItem => p.2.2.1 != p.1.1) := by
    apply (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.const false) (Primrec.const true)).of_eq
    intro p
    by_cases h : p.2.2.1 = p.1.1 <;> simp [h]
  have hf : Primrec (fun p : PrefixInput => p.2.2.2.filter (fun b => b.2.1 != p.1)) :=
    (listFilterPrimitive hkeep.to₂).comp Primrec.id hentries
  exact (hconstant.pair hf.to_comp).of_eq (fun _ => rfl)

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof.Numeric
