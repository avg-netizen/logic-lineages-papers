module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeComputationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeProof
open HyperWindowCode
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem any_calibration (xs : List Matrix) :
    WindowCode.any (xs.map Matrix.encode) = (Matrix.any xs).encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change 8 * Nat.pair p.encode (WindowCode.any (ps.map Matrix.encode)) + 7 =
      8 * Nat.pair p.encode (Matrix.any ps).encode + 7
    rw [ih]

private theorem left_calibration (i j : Nat) (e h k l : Int) (c : Nat) (p : Matrix) :
    HyperWindowCode.leftCases (input i j e h k l c p.encode) =
      (HyperWindow.leftCases i j e h k l c p).encode := by
  unfold HyperWindowCode.leftCases HyperWindow.leftCases
  rw [← any_calibration]
  apply congrArg WindowCode.any
  rw [List.map_map]
  apply List.map_congr_left
  intro n hn
  exact WindowCodeProof.matrix_calibration i (.numeral n)
    (Matrix.conjunction (HyperWindow.closeMatrix i j e h k l c) p)

private theorem right_calibration (i j : Nat) (e h k l : Int) (c : Nat) (p : Matrix) :
    HyperWindowCode.rightCases (input i j e h k l c p.encode) =
      (HyperWindow.rightCases i j e h k l c p).encode := by
  unfold HyperWindowCode.rightCases HyperWindow.rightCases
  rw [← any_calibration]
  apply congrArg WindowCode.any
  rw [List.map_map]
  apply List.map_congr_left
  intro n hn
  exact WindowCodeProof.matrix_calibration j (.numeral n)
    (Matrix.conjunction (HyperWindow.closeMatrix i j e h k l c) p)

private theorem equal_calibration (i j : Nat) (e h k l : Int) (c : Nat) (p : Matrix) :
    HyperWindowCode.equalCases (input i j e h k l c p.encode) =
      (HyperWindow.equalCases i j e h k l c p).encode :=
  WindowCodeProof.matrix_calibration i (shiftTerm (.variable j) (k - e))
    (Matrix.conjunction (.equal (HyperWindow.indexTerm i e) (HyperWindow.indexTerm j k))
      (.conjunction (HyperWindow.closeMatrix i j e h k l c) p))

theorem literalCalibration : HyperWindowCodeTargets.LiteralCalibration := by
  intro i j e h k l c p
  exact ⟨left_calibration i j e h k l c p, right_calibration i j e h k l c p,
    equal_calibration i j e h k l c p⟩

private theorem binary_primitive (base label : Nat) :
    Primrec₂ (fun a b : Nat => base * Nat.pair a b + label) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair)
    (Primrec.const label)
private theorem unary_primitive (base label : Nat) :
    Primrec (fun a : Nat => base * a + label) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec.id)
    (Primrec.const label)

private theorem numeral_primitive : Primrec WindowCode.numeral :=
  Primrec.nat_mul.comp (Primrec.const 10) Primrec.id
private theorem var_primitive : Primrec WindowCode.var := unary_primitive 10 1
private theorem phi_primitive : Primrec WindowCode.phi := unary_primitive 10 6
private theorem hyper_primitive : Primrec HyperWindowCode.hyper := unary_primitive 10 7
private theorem equal_primitive : Primrec₂ HyperWindowCode.equal := binary_primitive 8 2
private theorem less_primitive : Primrec₂ WindowCode.less := binary_primitive 8 3
private theorem negative_primitive : Primrec WindowCode.negative := unary_primitive 8 5
private theorem conjunction_primitive : Primrec₂ WindowCode.conjunction := binary_primitive 8 6
private theorem disjunction_primitive : Primrec₂ WindowCode.disjunction := binary_primitive 8 7
private theorem add_primitive : Primrec₂ WindowCode.add := binary_primitive 10 2
private theorem subtract_primitive : Primrec₂ WindowCode.subtract := binary_primitive 10 3
private theorem multiply_primitive : Primrec₂ WindowCode.multiply := binary_primitive 10 4

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
private theorem domain_primitive : Primrec₂ WindowCode.domain :=
  negative_primitive.comp (less_primitive.comp Primrec.fst
    (numeral_primitive.comp (toNat_primitive.comp
      (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd))))
private theorem atMost_primitive : Primrec₂ WindowCode.atMost :=
  negative_primitive.comp (less_primitive.comp Primrec.snd Primrec.fst)
private theorem index_primitive : Primrec₂ HyperWindowCode.index :=
  shift_primitive.comp (var_primitive.comp Primrec.fst) Primrec.snd

private theorem leftName_primitive : Primrec leftName := Primrec.fst.comp Primrec.fst
private theorem rightName_primitive : Primrec rightName := Primrec.snd.comp Primrec.fst
private theorem leftIndex_primitive : Primrec leftIndex :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
private theorem leftOuter_primitive : Primrec leftOuter :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
private theorem rightIndex_primitive : Primrec rightIndex :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem rightOuter_primitive : Primrec rightOuter :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem coefficient_primitive : Primrec coefficient :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
private theorem matrix_primitive : Primrec matrix :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem value_program {A : Type} [Primcodable A]
    {i : A → Nat} {e h : A → Int} (hi : Primrec i) (he : Primrec e) (hh : Primrec h) :
    Primrec (fun a => HyperWindowCode.value (i a) (e a) (h a)) :=
  phi_primitive.comp (shift_primitive.comp
    (hyper_primitive.comp (index_primitive.comp hi he)) hh)

private theorem domain_program {A : Type} [Primcodable A]
    {i : A → Nat} {e h : A → Int} (hi : Primrec i) (he : Primrec e) (hh : Primrec h) :
    Primrec (fun a => HyperWindowCode.domain (i a) (e a) (h a)) :=
  conjunction_primitive.comp (domain_primitive.comp (var_primitive.comp hi) he)
    (domain_primitive.comp (hyper_primitive.comp (index_primitive.comp hi he)) hh)

private theorem close_primitive : Primrec HyperWindowCode.close := by
  have hv := value_program leftName_primitive leftIndex_primitive leftOuter_primitive
  have hw := value_program rightName_primitive rightIndex_primitive rightOuter_primitive
  have hd := domain_program leftName_primitive leftIndex_primitive leftOuter_primitive
  have he := domain_program rightName_primitive rightIndex_primitive rightOuter_primitive
  exact conjunction_primitive.comp hd (conjunction_primitive.comp he
    (conjunction_primitive.comp (atMost_primitive.comp hw hv)
      (atMost_primitive.comp hv (multiply_primitive.comp coefficient_primitive hw))))

private theorem guarded_primitive : Primrec guarded :=
  conjunction_primitive.comp close_primitive matrix_primitive
private theorem leftBound_primitive : Primrec HyperWindowCode.leftBound :=
  HyperWindowProof.actualBoundPrograms.1.comp
    (leftIndex_primitive.pair (leftOuter_primitive.pair rightOuter_primitive))
private theorem rightBound_primitive : Primrec HyperWindowCode.rightBound :=
  HyperWindowProof.actualBoundPrograms.2.comp
    (leftOuter_primitive.pair (rightIndex_primitive.pair
      (rightOuter_primitive.pair coefficient_primitive)))

private theorem finite_cases_program {A : Type} [Primcodable A]
    {i B g : A → Nat} (hi : Primrec i) (hb : Primrec B) (hg : Primrec g) :
    Computable (fun a => WindowCode.any ((List.range (B a)).map (fun n =>
      WindowCode.matrixSubstitute (i a) (WindowCode.numeral n) (g a)))) := by
  have hstep : Computable₂ (fun a : A => fun p : Nat × Nat =>
      WindowCode.disjunction (WindowCode.matrixSubstitute (i a)
        (WindowCode.numeral p.1) (g a)) p.2) :=
    disjunction_primitive.to_comp.comp
      (WindowCodeProof.matrix_computable.comp
        ((hg.to_comp.comp Computable.fst).pair
          ((hi.to_comp.comp Computable.fst).pair
            (numeral_primitive.to_comp.comp (Computable.fst.comp Computable.snd)))))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr 0
    (Primrec.list_range.to_comp.comp hb.to_comp) (Computable.const 1) hstep).of_eq
  intro a
  simp only [WindowCode.any, List.foldr_map]

private theorem left_computable : Computable HyperWindowCode.leftCases :=
  finite_cases_program leftName_primitive leftBound_primitive guarded_primitive
private theorem right_computable : Computable HyperWindowCode.rightCases :=
  finite_cases_program rightName_primitive rightBound_primitive guarded_primitive

private theorem equal_computable : Computable HyperWindowCode.equalCases := by
  have hd : Primrec (fun p : Input => rightIndex p - leftIndex p) := by
    apply (IntegerAlgorithms.Proof.add_primitive.comp rightIndex_primitive
      (IntegerAlgorithms.Proof.negate_primitive.comp leftIndex_primitive)).of_eq
    intro p
    exact (sub_eq_add_neg _ _).symm
  have hr : Primrec (fun p : Input => WindowCode.shift (WindowCode.var (rightName p))
      (rightIndex p - leftIndex p)) :=
    shift_primitive.comp (var_primitive.comp rightName_primitive) hd
  have heq : Primrec (fun p : Input => HyperWindowCode.equal
      (HyperWindowCode.index (leftName p) (leftIndex p))
      (HyperWindowCode.index (rightName p) (rightIndex p))) :=
    equal_primitive.comp (index_primitive.comp leftName_primitive leftIndex_primitive)
      (index_primitive.comp rightName_primitive rightIndex_primitive)
  have hcode : Primrec (fun p : Input => WindowCode.conjunction
      (HyperWindowCode.equal (HyperWindowCode.index (leftName p) (leftIndex p))
        (HyperWindowCode.index (rightName p) (rightIndex p))) (guarded p)) :=
    conjunction_primitive.comp heq guarded_primitive
  exact WindowCodeProof.matrix_computable.comp
    (hcode.to_comp.pair (leftName_primitive.to_comp.pair hr.to_comp))

theorem actualCodeComputation : HyperWindowCodeTargets.ActualCodeComputation :=
  ⟨left_computable, right_computable, equal_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeProof
