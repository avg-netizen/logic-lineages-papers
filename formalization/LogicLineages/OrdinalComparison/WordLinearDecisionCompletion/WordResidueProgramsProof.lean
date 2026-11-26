module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidueLetterProof
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Proof
open PolynomialGraphCompletion
open LayeredComparison.IntegerAlgorithms.Proof

attribute [local irreducible] Nat.sqrt Nat.unpair kernelCounterResidue fastControlResidue

theorem letterAffinePrimitive : Primrec (fun p : Nat × Letter => letterAffine p.1 p.2) := by
  have htag : Primrec (fun p : Nat × Letter => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Letter => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : Nat × Letter => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hj : Primrec (fun p : Nat × Letter => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have he : Primrec (fun p : Nat × Letter => kernelCounterResidue p.2.2.1 p.2.2.2.1 p.1) :=
    KernelSourceCompletion.Proof.correctedKernelResidues.2.1.comp (hd.pair (hc.pair Primrec.fst))
  have hp : Primrec (fun p : Nat × Letter => fastControlResidue p.1) :=
    fastControlResiduePrimitiveRecursive.comp Primrec.fst
  apply (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
    ((Primrec.const (1 : Int)).pair hj)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4))
      ((Primrec.const (0 : Int)).pair (ofNat_primitive.comp he))
      ((Primrec.const (0 : Int)).pair (ofNat_primitive.comp hp)))).of_eq
  intro p
  rfl

theorem letterTailPrimitive : Primrec (fun p : Nat × Letter => letterTail p.1 p.2) := by
  have htag : Primrec (fun p : Nat × Letter => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Letter => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : Nat × Letter => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have he : Primrec (fun p : Nat × Letter => KernelSourceCompletion.residueTail p.2.2.1 p.2.2.2.1 0 p.1) :=
    (KernelSourceCompletion.Proof.correctedKernelResidues.2.2 0).comp
      (hd.pair (hc.pair Primrec.fst))
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (WordGuardCompletion.Proof.letterTail_primitive.comp Primrec.snd)
      Primrec.fst)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) he (Primrec.const 0))

theorem letterPrograms : Targets.LetterPrograms := ⟨letterAffinePrimitive, letterTailPrimitive⟩

theorem affinePrimitive : Primrec (fun p : Nat × Word => affine p.1 p.2) := by
  let A := Nat × Word
  have hp : Primrec (fun p : A × (Letter × Affine) => letterAffine p.1.1 p.2.1) :=
    letterAffinePrimitive.comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  have hs : Primrec (fun p : A × (Letter × Affine) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : A × (Letter × Affine) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hh : Primrec (fun p : A × (Letter × Affine) =>
      (p.2.2.1 * (letterAffine p.1.1 p.2.1).1,
        p.2.2.1 * (letterAffine p.1.1 p.2.1).2 + p.2.2.2)) :=
    (mul_primitive.comp hs (Primrec.fst.comp hp)).pair
      (add_primitive.comp (mul_primitive.comp hs (Primrec.snd.comp hp)) hb)
  have hf : Primrec (fun p : A => p.2.foldr (fun a q =>
      (q.1 * (letterAffine p.1 a).1, q.1 * (letterAffine p.1 a).2 + q.2)) (1, 0)) :=
    Primrec.list_foldr Primrec.snd (Primrec.const ((1, 0) : Affine)) hh.to₂
  apply hf.of_eq
  intro p
  rcases p with ⟨m, w⟩
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.foldr_cons, affine, ih]

theorem tailPrimitive : Primrec (fun p : Nat × Word => tail p.1 p.2) := by
  let A := Nat × Word
  have ht : Primrec (fun p : A × (Letter × Nat) => letterTail p.1.1 p.2.1) :=
    letterTailPrimitive.comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  have ho : Primrec (fun p : A × (Letter × Nat) => WordGuardCompletion.letterOffset p.2.1) :=
    WordGuardCompletion.Proof.letterOffset_primitive.comp (Primrec.fst.comp Primrec.snd)
  have hh : Primrec (fun p : A × (Letter × Nat) =>
      letterTail p.1.1 p.2.1 + WordGuardCompletion.letterOffset p.2.1 + p.2.2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp ht ho) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun p : A => p.2.foldr (fun a n =>
      letterTail p.1 a + WordGuardCompletion.letterOffset a + n) 0) :=
    Primrec.list_foldr Primrec.snd (Primrec.const 0) hh.to₂
  apply hf.of_eq
  intro p
  rcases p with ⟨m, w⟩
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.foldr_cons, tail, ih]

theorem wordPrograms : Targets.WordPrograms := ⟨affinePrimitive, tailPrimitive⟩

theorem integerSumPrimitive : Primrec (fun xs : List Int => xs.sum) := by
  have hs : Primrec (fun p : List Int × (Int × Int) => p.2.1 + p.2.2) :=
    add_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Int => xs.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const (0 : Int)) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, List.sum_cons, ih]

theorem naturalSumPrimitive : Primrec (fun xs : List Nat => xs.sum) := by
  have hs : Primrec (fun p : List Nat × (Nat × Nat) => p.2.1 + p.2.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Nat => xs.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, List.sum_cons, ih]

theorem rowPrimitive : Primrec (fun p : Nat × Row => row p.1 p.2) := by
  let A := Nat × Row
  let Item := Int × (Nat × Word)
  have hm : Primrec (fun p : A × Item => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : A × Item => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : A × Item => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : A × Item => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun p : A × Item => affine p.1.1 p.2.2.2) :=
    affinePrimitive.comp (hm.pair hw)
  have ho : Primrec (fun p : A × Item => p.2.1 * (affine p.1.1 p.2.2.2).2) :=
    mul_primitive.comp hc (Primrec.snd.comp hf)
  have he : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hconstant : Primrec (fun p : A => p.2.1 +
      (p.2.2.map (fun a => a.1 * (affine p.1 a.2.2).2)).sum) :=
    add_primitive.comp (Primrec.fst.comp Primrec.snd)
      (integerSumPrimitive.comp (Primrec.list_map he ho.to₂))
  have hraw : Primrec (fun p : A × Item =>
      (p.2.1 * (affine p.1.1 p.2.2.2).1, (p.2.2.1, ([] : Word)))) :=
    (mul_primitive.comp hc (Primrec.fst.comp hf)).pair (hn.pair (Primrec.const []))
  exact hconstant.pair (Primrec.list_map he hraw.to₂)

theorem rowTailPrimitive : Primrec (fun p : Nat × Row => rowTail p.1 p.2) := by
  have he : Primrec (fun p : Nat × Row => p.2.2) := Primrec.snd.comp Primrec.snd
  have ht : Primrec (fun p : (Nat × Row) × (Int × (Nat × Word)) => tail p.1.1 p.2.2.2) :=
    tailPrimitive.comp ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact naturalSumPrimitive.comp (Primrec.list_map he ht.to₂)

theorem rowPrograms : Targets.RowPrograms := ⟨rowPrimitive, rowTailPrimitive⟩

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Proof
