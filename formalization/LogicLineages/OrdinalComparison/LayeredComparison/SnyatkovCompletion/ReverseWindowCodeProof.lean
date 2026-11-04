module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeComputationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowCodeProof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem any_calibration (xs : List Matrix) :
    WindowCode.any (xs.map Matrix.encode) = (Matrix.any xs).encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change 8 * Nat.pair p.encode (WindowCode.any (ps.map Matrix.encode)) + 7 =
      8 * Nat.pair p.encode (Matrix.any ps).encode + 7
    rw [ih]

theorem literalCodeCalibration : ReverseWindowTargets.LiteralCodeCalibration := by
  intro i anchor e c p
  unfold ReverseWindow.Code.finiteCases ReverseWindow.finiteCases
  rw [← any_calibration]
  apply congrArg WindowCode.any
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  exact WindowCodeProof.matrix_calibration i (ReverseWindow.replacementTerm anchor e d)
    (Matrix.conjunction (ReverseWindow.closeMatrix i anchor e c) p)

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

theorem actualCodeComputation : ReverseWindowTargets.ActualCodeComputation := by
  let P := ReverseWindow.Code.Input
  have hi : Primrec (fun p : P => p.1) := Primrec.fst
  have ha : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : P => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hp : Primrec (fun p : P => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hv := var_primitive.comp hi
  have hs := shift_primitive.comp hv he
  have hpa := phi_primitive.comp ha
  have hps := phi_primitive.comp hs
  have hdom := domain_primitive.comp hv he
  have hclose : Primrec (fun p : P => ReverseWindow.Code.close p.1 p.2.1 p.2.2.1 p.2.2.2.1) :=
    conjunction_primitive.comp hdom
      (conjunction_primitive.comp (atMost_primitive.comp hps hpa)
        (atMost_primitive.comp hpa (multiply_primitive.comp hc hps)))
  have hguard : Primrec (fun p : P => WindowCode.conjunction
      (ReverseWindow.Code.close p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2) :=
    conjunction_primitive.comp hclose hp
  have hrepl : Primrec₂ (fun p : P => fun d : Nat => ReverseWindow.Code.replacement p.2.1 p.2.2.1 d) :=
    shift_primitive.comp
      (subtract_primitive.comp (ha.comp Primrec.fst) (numeral_primitive.comp Primrec.snd))
      (IntegerAlgorithms.Proof.negate_primitive.comp (he.comp Primrec.fst))
  have hbranch : Computable₂ (fun p : P => fun d : Nat =>
      WindowCode.matrixSubstitute p.1 (ReverseWindow.Code.replacement p.2.1 p.2.2.1 d)
        (WindowCode.conjunction (ReverseWindow.Code.close p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2)) :=
    WindowCodeProof.matrix_computable.comp ((hguard.to_comp.comp Computable.fst).pair
      ((hi.to_comp.comp Computable.fst).pair hrepl.to_comp))
  have hstep : Computable₂ (fun p : P => fun state : Nat × Nat =>
      WindowCode.disjunction
        (WindowCode.matrixSubstitute p.1 (ReverseWindow.Code.replacement p.2.1 p.2.2.1 state.1)
          (WindowCode.conjunction (ReverseWindow.Code.close p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2)) state.2) :=
    disjunction_primitive.to_comp.comp
      (hbranch.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  have hlist : Computable (fun p : P => List.range (p.2.2.2.1 + 1)) :=
    Primrec.list_range.to_comp.comp (Primrec.nat_add.comp hc (Primrec.const 1)).to_comp
  apply (ComparisonAssembly.computable_foldr 0 hlist (Computable.const 1) hstep).of_eq
  intro p
  simp only [ReverseWindow.Code.finiteCases, WindowCode.any, List.foldr_map]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindowCodeProof
