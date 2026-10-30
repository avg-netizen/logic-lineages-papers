module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantCodeTargets
public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminantEffectivity
public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCodeEffectivity

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode

private abbrev Parameters := ℕ × ℕ × DensePolynomial.Code

private theorem nat_power_primitive_recursive : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem outerAdd_primitive_recursive : Primrec₂ outerAdd := by
  have hl := Primrec.list_range.comp (Primrec.nat_max.comp
    (Primrec.list_length.comp (show Primrec (fun t : OuterCode × OuterCode => t.1) from Primrec.fst))
    (Primrec.list_length.comp (show Primrec (fun t : OuterCode × OuterCode => t.2) from Primrec.snd)))
  have ha : Primrec (fun t : (OuterCode × OuterCode) × ℕ => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun t : (OuterCode × OuterCode) × ℕ => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun t : (OuterCode × OuterCode) × ℕ => t.2) := Primrec.snd
  have hca := (Primrec.list_getD ([] : DensePolynomial.Code)).comp ha hi
  have hcb := (Primrec.list_getD ([] : DensePolynomial.Code)).comp hb hi
  have hs := DensePolynomial.add_primitive_recursive.comp hca hcb
  have h := Primrec.list_map hl hs.to₂
  exact h.of_eq (fun _ => rfl)

private theorem outerMonomial_eq_rec (a : DensePolynomial.Code) (k : ℕ) :
    outerMonomial a k = Nat.rec (motive := fun _ => OuterCode) [a]
      (fun _ acc => [] :: acc) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [outerMonomial, List.replicate_succ, List.cons_append] using
      congrArg (fun acc : OuterCode => [] :: acc) ih

theorem outerMonomial_primitive_recursive : Primrec₂ outerMonomial := by
  have hz : Primrec (fun t : DensePolynomial.Code × ℕ => ([t.1] : OuterCode)) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  have hs : Primrec (fun t : (DensePolynomial.Code × ℕ) × (ℕ × OuterCode) =>
      ([] : DensePolynomial.Code) :: t.2.2) :=
    Primrec.list_cons.comp (Primrec.const ([] : DensePolynomial.Code))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec' (show Primrec (fun t : DensePolynomial.Code × ℕ => t.2)
    from Primrec.snd) hz hs.to₂
  exact h.of_eq (fun t => (outerMonomial_eq_rec t.1 t.2).symm)

private def codeRow (p : Parameters) (k : ℕ) (a : OuterCode) : OuterCode :=
  (List.range (p.1 + 1)).foldr (fun j inner =>
    if k + 1 ≤ j then outerAdd
      (outerMonomial (BoxPolynomialCode.monomial
        (p.2.2.getD j RationalCode.zero) (p.2.1 ^ k)) (j - (k + 1))) inner else inner) a

private theorem codeRow_step_primitive_recursive :
    Primrec (fun t : (Parameters × ℕ) × (ℕ × OuterCode) =>
      if t.1.2 + 1 ≤ t.2.1 then outerAdd
        (outerMonomial (BoxPolynomialCode.monomial
          (t.1.1.2.2.getD t.2.1 RationalCode.zero) (t.1.1.2.1 ^ t.1.2))
          (t.2.1 - (t.1.2 + 1))) t.2.2 else t.2.2) := by
  have hp : Primrec (fun t : (Parameters × ℕ) × (ℕ × OuterCode) => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb := (show Primrec (fun p : Parameters => p.2.1) from Primrec.fst.comp Primrec.snd).comp hp
  have hf := (show Primrec (fun p : Parameters => p.2.2) from Primrec.snd.comp Primrec.snd).comp hp
  have hk : Primrec (fun t : (Parameters × ℕ) × (ℕ × OuterCode) => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hj : Primrec (fun t : (Parameters × ℕ) × (ℕ × OuterCode) => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun t : (Parameters × ℕ) × (ℕ × OuterCode) => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hc := (Primrec.list_getD RationalCode.zero).comp hf hj
  have hpow := nat_power_primitive_recursive.comp hb hk
  have hm := BoxPolynomialCode.monomial_primitive_recursive.comp hc hpow
  have hsucc := Primrec.nat_add.comp hk (Primrec.const 1)
  have he := Primrec.nat_sub.comp hj hsucc
  have ho := outerMonomial_primitive_recursive.comp hm he
  have hadd := outerAdd_primitive_recursive.comp ho ha
  exact (Primrec.ite (Primrec.nat_le.comp hsucc hj) hadd ha).of_eq (fun _ => rfl)

private theorem codeRow_primitive_recursive :
    Primrec (fun t : (Parameters × ℕ) × OuterCode => codeRow t.1.1 t.1.2 t.2) := by
  have hn : Primrec (fun t : (Parameters × ℕ) × OuterCode => t.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hl := Primrec.list_range.comp (Primrec.nat_add.comp hn (Primrec.const 1))
  have hi : Primrec (fun t : ((Parameters × ℕ) × OuterCode) × (ℕ × OuterCode) =>
      (t.1.1, t.2)) := (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  have hs := codeRow_step_primitive_recursive.comp hi
  have h := Primrec.list_foldr hl (show Primrec
    (fun t : (Parameters × ℕ) × OuterCode => t.2) from Primrec.snd) hs.to₂
  exact h.of_eq (fun _ => rfl)

theorem generating_primitive_recursive :
    Primrec (fun t : ℕ × ℕ × DensePolynomial.Code => generating t.1 t.2.1 t.2.2) := by
  have hi : Primrec (fun t : Parameters × (ℕ × OuterCode) => ((t.1, t.2.1), t.2.2)) :=
    (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  have hs := codeRow_primitive_recursive.comp hi
  have hl := Primrec.list_range.comp (show Primrec (fun t : Parameters => t.1) from Primrec.fst)
  have h := Primrec.list_foldr hl (Primrec.const ([] : OuterCode)) hs.to₂
  exact h.of_eq (fun _ => rfl)

private theorem sylvesterEntry_primitive_recursive :
    Primrec (fun t : Parameters × (ℕ × ℕ) =>
      sylvesterEntry t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2) := by
  have hp : Primrec (fun t : Parameters × (ℕ × ℕ) => t.1) := Primrec.fst
  have hn := (show Primrec (fun p : Parameters => p.1) from Primrec.fst).comp hp
  have hf := (show Primrec (fun p : Parameters => p.2.2) from Primrec.snd.comp Primrec.snd).comp hp
  have hi : Primrec (fun t : Parameters × (ℕ × ℕ) => t.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun t : Parameters × (ℕ × ℕ) => t.2.2) := Primrec.snd.comp Primrec.snd
  have hg := generating_primitive_recursive.comp hp
  have hleftIndex := Primrec.nat_sub.comp hi hj
  have hleftValue := (Primrec.list_getD ([] : DensePolynomial.Code)).comp hg hleftIndex
  have hnm1 := Primrec.nat_sub.comp hn (Primrec.const 1)
  have hleftCond := (Primrec.nat_le.comp hj hi).and
    (Primrec.nat_le.comp hi (Primrec.nat_add.comp hj hnm1))
  have hleft := Primrec.ite hleftCond hleftValue (Primrec.const [])
  have hshift := Primrec.nat_sub.comp hj hn
  have hrightIndex := Primrec.nat_sub.comp hi hshift
  have hrightCoefficient := (Primrec.list_getD RationalCode.zero).comp hf hrightIndex
  have hrightValue := Primrec.list_cons.comp hrightCoefficient (Primrec.const [])
  have hrightCond := (Primrec.nat_le.comp hshift hi).and
    (Primrec.nat_le.comp hi (Primrec.nat_add.comp hshift hn))
  have hright := Primrec.ite hrightCond hrightValue (Primrec.const [])
  exact (Primrec.ite (Primrec.nat_lt.comp hj hn) hleft hright).of_eq (fun _ => rfl)

theorem matrix_primitive_recursive :
    Primrec (fun t : ℕ × ℕ × DensePolynomial.Code => matrix t.1 t.2.1 t.2.2) := by
  have hn : Primrec (fun p : Parameters => p.1) := Primrec.fst
  have hd := Primrec.nat_add.comp hn (Primrec.nat_sub.comp hn (Primrec.const 1))
  have hs := Primrec.nat_mul.comp hd hd
  have hl := Primrec.list_range.comp hs
  have hdim := hd.comp (show Primrec (fun t : Parameters × ℕ => t.1) from Primrec.fst)
  have hdiv := Primrec.nat_div.comp (show Primrec (fun t : Parameters × ℕ => t.2) from Primrec.snd) hdim
  have hmod := Primrec.nat_mod.comp (show Primrec (fun t : Parameters × ℕ => t.2) from Primrec.snd) hdim
  have hi := (show Primrec (fun t : Parameters × ℕ => t.1) from Primrec.fst).pair (hdiv.pair hmod)
  have he := sylvesterEntry_primitive_recursive.comp hi
  have h := Primrec.list_map hl he.to₂
  exact h.of_eq (fun _ => rfl)

theorem obstruction_primitive_recursive :
    Primrec (fun t : ℕ × ℕ × DensePolynomial.Code => obstruction t.1 t.2.1 t.2.2) := by
  have hn : Primrec (fun p : Parameters => p.1) := Primrec.fst
  have hd := Primrec.nat_add.comp hn (Primrec.nat_sub.comp hn (Primrec.const 1))
  have h := NumericDeterminant.determinant_primitive_recursive.comp hd matrix_primitive_recursive
  exact h.of_eq (fun _ => rfl)

theorem operations_primitive_recursive : Targets.spectralResultantCodePrimitiveRecursive :=
  ⟨outerAdd_primitive_recursive, outerMonomial_primitive_recursive, generating_primitive_recursive,
    matrix_primitive_recursive, obstruction_primitive_recursive⟩

end LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode
