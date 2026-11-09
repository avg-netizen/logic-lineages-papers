module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeComputationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalProof
open PhiInterval
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem any_calibration (xs : List Matrix) :
    WindowCode.any (xs.map Matrix.encode) = (Matrix.any xs).encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change 8 * Nat.pair p.encode (WindowCode.any (ps.map Matrix.encode)) + 7 =
      8 * Nat.pair p.encode (Matrix.any ps).encode + 7
    rw [ih]

theorem fromStart_calibration (i a : Nat) (shift : Int) (m : Nat)
    (lower upper residue start : Term) :
    Code.fromStart i a shift m lower.encode upper.encode residue.encode start.encode =
      (fromStart i a shift m lower upper residue start).encode := by
  unfold Code.fromStart fromStart
  rw [← any_calibration]
  apply congrArg WindowCode.any
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  exact WindowCodeProof.matrix_calibration i (.add start (.numeral d))
    (interval i a shift m lower upper residue)

theorem literalCodeCalibration : PhiIntervalTargets.LiteralCodeCalibration := by
  intro i a shift m lower upper residue
  unfold Code.project project
  change WindowCode.disjunction
    (WindowCode.conjunction (initialGuard a shift lower).encode
      (Code.fromStart i a shift m lower.encode upper.encode residue.encode (initialStart shift).encode))
    (WindowCode.conjunction (WindowCode.negative (initialGuard a shift lower).encode)
      (Code.fromStart i a shift m lower.encode upper.encode residue.encode (tailStart a shift lower).encode)) = _
  rw [fromStart_calibration, fromStart_calibration]
  rfl

private theorem binary_primitive (base tag : Nat) :
    Primrec₂ (fun a b : Nat => base * Nat.pair a b + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair)
    (Primrec.const tag)
private theorem unary_primitive (base tag : Nat) :
    Primrec (fun a : Nat => base * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec.id)
    (Primrec.const tag)
private theorem add_primitive : Primrec₂ WindowCode.add := binary_primitive 10 2
private theorem subtract_primitive : Primrec₂ WindowCode.subtract := binary_primitive 10 3
private theorem multiply_primitive : Primrec₂ WindowCode.multiply := binary_primitive 10 4
private theorem divide_primitive : Primrec₂ Code.divide := binary_primitive 10 5
private theorem inverse_primitive : Primrec DominantBoundary.Code.inverse := unary_primitive 10 8
private theorem phi_primitive : Primrec WindowCode.phi := unary_primitive 10 6
private theorem var_primitive : Primrec WindowCode.var := unary_primitive 10 1
private theorem less_primitive : Primrec₂ WindowCode.less := binary_primitive 8 3
private theorem equal_primitive : Primrec₂ (fun a b : Nat => 8 * Nat.pair a b + 2) := binary_primitive 8 2
private theorem negative_primitive : Primrec WindowCode.negative := unary_primitive 8 5
private theorem conjunction_primitive : Primrec₂ WindowCode.conjunction := binary_primitive 8 6
private theorem disjunction_primitive : Primrec₂ WindowCode.disjunction := binary_primitive 8 7
private theorem atMost_primitive : Primrec₂ WindowCode.atMost :=
  negative_primitive.comp (less_primitive.comp Primrec.snd Primrec.fst)
private theorem numeral_primitive : Primrec WindowCode.numeral :=
  Primrec.nat_mul.comp (Primrec.const 10) Primrec.id

private theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp IntegerAlgorithms.Proof.sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) IntegerAlgorithms.Proof.abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem shift_primitive : Primrec₂ WindowCode.shift :=
  subtract_primitive.comp
    (add_primitive.comp Primrec.fst (numeral_primitive.comp (toNat_primitive.comp Primrec.snd)))
    (numeral_primitive.comp (toNat_primitive.comp
      (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd)))
private theorem crossing_primitive : Primrec₂ Code.crossingTerm :=
  add_primitive.comp
    (inverse_primitive.comp (divide_primitive.comp Primrec.fst
      (subtract_primitive.comp Primrec.snd (Primrec.const 10)))) (Primrec.const 10)
private theorem residue_primitive : Primrec₂ Code.residueTerm :=
  subtract_primitive.comp Primrec.snd
    (multiply_primitive.comp Primrec.fst (divide_primitive.comp Primrec.fst Primrec.snd))

private abbrev GuardInput := Nat × (Int × Nat)
private theorem initialGuard_primitive : Primrec (fun q : GuardInput =>
    Code.initialGuard q.1 q.2.1 q.2.2) := by
  have ha : Primrec (fun q : GuardInput => q.1) := Primrec.fst
  have he : Primrec (fun q : GuardInput => q.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun q : GuardInput => q.2.2) := Primrec.snd.comp Primrec.snd
  exact atMost_primitive.comp hl (multiply_primitive.comp ha
    (phi_primitive.comp (numeral_primitive.comp (toNat_primitive.comp he))))
private theorem tailStart_primitive : Primrec (fun q : GuardInput =>
    Code.tailStart q.1 q.2.1 q.2.2) := by
  have ha : Primrec (fun q : GuardInput => q.1) := Primrec.fst
  have he : Primrec (fun q : GuardInput => q.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun q : GuardInput => q.2.2) := Primrec.snd.comp Primrec.snd
  exact shift_primitive.comp (crossing_primitive.comp ha hl)
    (IntegerAlgorithms.Proof.negate_primitive.comp he)

attribute [local irreducible] Code.crossingTerm Code.residueTerm Code.initialGuard Code.tailStart

private theorem interval_primitive : Primrec (fun q : Code.Input =>
    Code.interval q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2) := by
  let Q := Code.Input
  have hi : Primrec (fun q : Q => q.1) := Primrec.fst
  have ha : Primrec (fun q : Q => q.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun q : Q => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec (fun q : Q => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hl : Primrec (fun q : Q => q.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hu : Primrec (fun q : Q => q.2.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hr : Primrec (fun q : Q => q.2.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hv : Primrec (fun q : Q => WindowCode.var q.1) := var_primitive.comp hi
  have hvalue : Primrec (fun q : Q => WindowCode.multiply q.2.1
      (WindowCode.phi (WindowCode.shift (WindowCode.var q.1) q.2.2.1))) :=
    multiply_primitive.comp ha (phi_primitive.comp (shift_primitive.comp hv he))
  have hdom : Primrec (fun q : Q => WindowCode.domain (WindowCode.var q.1) q.2.2.1) :=
    negative_primitive.comp (less_primitive.comp hv
      (numeral_primitive.comp (toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp he))))
  exact conjunction_primitive.comp hdom
    (conjunction_primitive.comp (atMost_primitive.comp hl hvalue)
      (conjunction_primitive.comp (atMost_primitive.comp hvalue hu)
        (equal_primitive.comp (residue_primitive.comp hm hv) (residue_primitive.comp hm hr))))

attribute [local irreducible] Code.interval

private theorem any_primitive : Primrec WindowCode.any :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (disjunction_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem map_computable {A B C : Type} [Primcodable A] [Primcodable B]
    [Primcodable C] [Inhabited B] {xs : A → List B} {f : A → B → C}
    (hx : Computable xs) (hf : Computable₂ f) : Computable (fun a => (xs a).map (f a)) := by
  have hs : Computable₂ (fun a : A => fun p : B × List C => f a p.1 :: p.2) :=
    Primrec.list_cons.to_comp.comp
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil => rfl
  | cons b bs ih => simp only [List.foldr_cons, List.map_cons, ih]

private theorem fromStart_computable (start : Code.Input → Nat) (hs : Computable start) :
    Computable (fun q : Code.Input => Code.fromStart q.1 q.2.1 q.2.2.1 q.2.2.2.1
      q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2 (start q)) := by
  let Q := Code.Input
  have hi : Primrec (fun q : Q => q.1) := Primrec.fst
  have hm : Primrec (fun q : Q => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hbranch : Computable₂ (fun q : Q => fun d : Nat =>
      WindowCode.matrixSubstitute q.1 (WindowCode.add (start q) (WindowCode.numeral d))
        (Code.interval q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)) :=
    WindowCodeProof.matrix_computable.comp
      ((interval_primitive.to_comp.comp Computable.fst).pair
        ((hi.to_comp.comp Computable.fst).pair
          (add_primitive.to_comp.comp (hs.comp Computable.fst)
            (numeral_primitive.to_comp.comp Computable.snd))))
  have hlist : Computable (fun q : Q => List.range q.2.2.2.1) :=
    Primrec.list_range.to_comp.comp hm.to_comp
  exact any_primitive.to_comp.comp (map_computable hlist hbranch)

attribute [local irreducible] Code.fromStart

theorem actualNumericProgram : PhiIntervalTargets.ActualNumericProgram := by
  let Q := Code.Input
  have ha : Primrec (fun q : Q => q.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun q : Q => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun q : Q => q.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hg : Primrec (fun q : Q => Code.initialGuard q.2.1 q.2.2.1 q.2.2.2.2.1) :=
    initialGuard_primitive.comp (ha.pair (he.pair hl))
  have hzero : Primrec (fun q : Q => Code.initialStart q.2.2.1) :=
    numeral_primitive.comp (toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp he))
  have htail : Primrec (fun q : Q => Code.tailStart q.2.1 q.2.2.1 q.2.2.2.2.1) :=
    tailStart_primitive.comp (ha.pair (he.pair hl))
  exact disjunction_primitive.to_comp.comp
    (conjunction_primitive.to_comp.comp hg.to_comp
      (fromStart_computable (fun q : Q => Code.initialStart q.2.2.1) hzero.to_comp))
    (conjunction_primitive.to_comp.comp (negative_primitive.to_comp.comp hg.to_comp)
      (fromStart_computable (fun q : Q => Code.tailStart q.2.1 q.2.2.1 q.2.2.2.2.1) htail.to_comp))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalProof
