module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeComputationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowCodeProof
open LinearWindow.Code
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem any_calibration (xs : List Matrix) :
    WindowCode.any (xs.map Matrix.encode) = (Matrix.any xs).encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change 8 * Nat.pair p.encode (WindowCode.any (ps.map Matrix.encode)) + 7 =
      8 * Nat.pair p.encode (Matrix.any ps).encode + 7
    rw [ih]

private theorem guard_calibration (i j : Nat) (leftKind rightKind : Bool)
    (e h k l : Int) (a code : Nat) :
    LinearWindow.Code.guard (input i j leftKind rightKind e h k l a code) =
      (LinearWindow.guard i j leftKind rightKind e h k l a).encode := by
  cases leftKind <;> cases rightKind <;> rfl

theorem literalCodeCalibration : LinearWindowTargets.LiteralCodeCalibration := by
  intro i j leftKind rightKind e h k l a p
  unfold LinearWindow.Code.finiteCases LinearWindow.finiteCases
  rw [← any_calibration]
  apply congrArg WindowCode.any
  rw [List.map_map]
  apply List.map_congr_left
  intro n hn
  rw [guard_calibration]
  exact WindowCodeProof.matrix_calibration j (.numeral n)
    (Matrix.conjunction (LinearWindow.guard i j leftKind rightKind e h k l a) p)

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

private theorem leftName_primitive : Primrec leftName := Primrec.fst.comp Primrec.fst
private theorem rightName_primitive : Primrec rightName := Primrec.snd.comp Primrec.fst
private theorem leftKind_primitive : Primrec leftKind :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
private theorem rightKind_primitive : Primrec rightKind :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
private theorem leftIndex_primitive : Primrec leftIndex :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem leftOuter_primitive : Primrec leftOuter :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem rightIndex_primitive : Primrec rightIndex :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem rightOuter_primitive : Primrec rightOuter :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem coefficient_primitive : Primrec coefficient :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem matrix_primitive : Primrec matrix :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem value_program {A : Type} [Primcodable A] {i : A → Nat}
    {kind : A → Bool} {e h : A → Int} (hi : Primrec i) (hk : Primrec kind)
    (he : Primrec e) (hh : Primrec h) :
    Primrec (fun a => LinearWindow.Code.value (i a) (kind a) (e a) (h a)) := by
  have hindex := shift_primitive.comp (var_primitive.comp hi) he
  exact Primrec.ite (Primrec.eq.comp hk (Primrec.const true))
    (phi_primitive.comp (shift_primitive.comp (hyper_primitive.comp hindex) hh))
    (phi_primitive.comp hindex)

private theorem domain_program {A : Type} [Primcodable A] {i : A → Nat}
    {kind : A → Bool} {e h : A → Int} (hi : Primrec i) (hk : Primrec kind)
    (he : Primrec e) (hh : Primrec h) :
    Primrec (fun a => LinearWindow.Code.domain (i a) (kind a) (e a) (h a)) := by
  have hv := var_primitive.comp hi
  have hbase := domain_primitive.comp hv he
  have hindex := shift_primitive.comp hv he
  exact Primrec.ite (Primrec.eq.comp hk (Primrec.const true))
    (conjunction_primitive.comp hbase
      (domain_primitive.comp (hyper_primitive.comp hindex) hh)) hbase

private theorem guard_primitive : Primrec LinearWindow.Code.guard := by
  have hv := value_program leftName_primitive leftKind_primitive leftIndex_primitive leftOuter_primitive
  have hw := value_program rightName_primitive rightKind_primitive rightIndex_primitive rightOuter_primitive
  have hd := domain_program leftName_primitive leftKind_primitive leftIndex_primitive leftOuter_primitive
  have he := domain_program rightName_primitive rightKind_primitive rightIndex_primitive rightOuter_primitive
  exact conjunction_primitive.comp hd (conjunction_primitive.comp he
    (conjunction_primitive.comp (atMost_primitive.comp hw hv)
      (atMost_primitive.comp hv (multiply_primitive.comp coefficient_primitive
        (var_primitive.comp rightName_primitive)))))

private theorem bound_primitive : Primrec LinearWindow.Code.bound :=
  LinearWindowProof.actualBoundProgram.comp
    (rightKind_primitive.pair (rightIndex_primitive.pair
      (rightOuter_primitive.pair coefficient_primitive)))

theorem actualCodeComputation : LinearWindowTargets.ActualCodeComputation := by
  have hg : Primrec (fun p : Input => WindowCode.conjunction (LinearWindow.Code.guard p) (matrix p)) :=
    conjunction_primitive.comp guard_primitive matrix_primitive
  have hstep : Computable₂ (fun p : Input => fun state : Nat × Nat =>
      WindowCode.disjunction (WindowCode.matrixSubstitute (rightName p)
        (WindowCode.numeral state.1)
        (WindowCode.conjunction (LinearWindow.Code.guard p) (matrix p))) state.2) :=
    disjunction_primitive.to_comp.comp
      (WindowCodeProof.matrix_computable.comp
        ((hg.to_comp.comp Computable.fst).pair
          ((rightName_primitive.to_comp.comp Computable.fst).pair
            (numeral_primitive.to_comp.comp (Computable.fst.comp Computable.snd)))))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr 0
    (Primrec.list_range.to_comp.comp bound_primitive.to_comp) (Computable.const 1) hstep).of_eq
  intro p
  simp only [LinearWindow.Code.finiteCases, WindowCode.any, List.foldr_map]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowCodeProof
