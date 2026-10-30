module

public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCodeTargets
public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialEffectivity

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode

private theorem nat_power_primitive_recursive : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem digitIndex_primitive_recursive :
    Primrec (fun t : ℕ × ℕ × ℕ × ℕ => digitIndex t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  let hb : Primrec (fun t : ℕ × ℕ × ℕ × ℕ => t.1) := Primrec.fst
  let hc : Primrec (fun t : ℕ × ℕ × ℕ × ℕ => t.2.1) := Primrec.fst.comp Primrec.snd
  let hk : Primrec (fun t : ℕ × ℕ × ℕ × ℕ => t.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h : Primrec (fun t : ℕ × ℕ × ℕ × ℕ =>
      Nat.rec (motive := fun _ => ℕ) 0
        (fun i acc => acc + ((t.2.2.1 / t.1 ^ i) % t.1) * t.2.1 ^ i) t.2.2.2) :=
    Primrec.nat_rec' (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)
      ((Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.nat_mul.comp
          (Primrec.nat_mod.comp
            (Primrec.nat_div.comp (hk.comp Primrec.fst)
              (nat_power_primitive_recursive.comp (hb.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
            (hb.comp Primrec.fst))
          (nat_power_primitive_recursive.comp (hc.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))).to₂)
  apply h.of_eq
  intro t
  induction t.2.2.2 with
  | zero => rfl
  | succ i ih => simp only [Nat.rec_add_one, digitIndex, ih]

theorem monomial_primitive_recursive : Primrec₂ monomial :=
  DensePolynomial.scale_primitive_recursive.comp Primrec.fst
    (DensePolynomial.power_primitive_recursive.comp
      (Primrec.const [RationalCode.zero, RationalCode.one]) Primrec.snd)

private abbrev RebaseContext := ℕ × ℕ × ℕ × Code

private theorem rebaseStep_primitive_recursive :
    Primrec (fun t : RebaseContext × (ℕ × Code) =>
      DensePolynomial.add t.2.2 (monomial
        (t.1.2.2.2.getD t.2.1 RationalCode.zero)
        (digitIndex t.1.2.1 t.1.2.2.1 t.2.1 t.1.1))) := by
  have hn : Primrec (fun t : RebaseContext × (ℕ × Code) => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun t : RebaseContext × (ℕ × Code) => t.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hc : Primrec (fun t : RebaseContext × (ℕ × Code) => t.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have ha : Primrec (fun t : RebaseContext × (ℕ × Code) => t.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hk : Primrec (fun t : RebaseContext × (ℕ × Code) => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hacc : Primrec (fun t : RebaseContext × (ℕ × Code) => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hinput := hb.pair (hc.pair (hk.pair hn))
  have hindex := digitIndex_primitive_recursive.comp hinput
  have hcoeff := (Primrec.list_getD RationalCode.zero).comp ha hk
  have hm := monomial_primitive_recursive.comp hcoeff hindex
  exact DensePolynomial.add_primitive_recursive.comp hacc hm

private theorem rebaseAux_eq_rec (n B C : ℕ) (a : Code) (m : ℕ) :
    rebaseAux n B C a m = Nat.rec (motive := fun _ => Code) []
      (fun k acc => DensePolynomial.add acc
        (monomial (a.getD k RationalCode.zero) (digitIndex B C k n))) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change DensePolynomial.add (rebaseAux n B C a m)
      (monomial (a.getD m RationalCode.zero) (digitIndex B C m n)) =
      DensePolynomial.add (Nat.rec (motive := fun _ => Code) []
        (fun k acc => DensePolynomial.add acc
          (monomial (a.getD k RationalCode.zero) (digitIndex B C k n))) m)
        (monomial (a.getD m RationalCode.zero) (digitIndex B C m n))
    exact congrArg (fun acc => DensePolynomial.add acc
      (monomial (a.getD m RationalCode.zero) (digitIndex B C m n))) ih

private theorem rebaseAux_primitive_recursive :
    Primrec (fun t : RebaseContext × ℕ =>
      rebaseAux t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2 t.2) := by
  have hz : Primrec (fun _ : RebaseContext => ([] : Code)) := Primrec.const []
  have h := Primrec.nat_rec hz rebaseStep_primitive_recursive.to₂
  exact Primrec.of_eq (g := fun t : RebaseContext × ℕ =>
    rebaseAux t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2 t.2) h
    (fun t => (rebaseAux_eq_rec t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2 t.2).symm)

theorem rebase_primitive_recursive :
    Primrec (fun t : ℕ × ℕ × ℕ × Code => rebase t.1 t.2.1 t.2.2.1 t.2.2.2) :=
  rebaseAux_primitive_recursive.comp (Primrec.id.pair
    (nat_power_primitive_recursive.comp (Primrec.fst.comp Primrec.snd) Primrec.fst))

theorem operations_primitive_recursive : Targets.boxCodeOperationsPrimitiveRecursive :=
  ⟨digitIndex_primitive_recursive, monomial_primitive_recursive, rebase_primitive_recursive⟩

end LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode
