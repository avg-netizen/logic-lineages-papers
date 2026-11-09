module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeComputationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryProof
open DominantBoundary
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem center_calibration (a : Nat) (lower : Term) :
    Code.center a lower.encode = (center a lower).encode := rfl

private theorem any_calibration (xs : List Matrix) :
    WindowCode.any (xs.map Matrix.encode) = (Matrix.any xs).encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change 8 * Nat.pair p.encode (WindowCode.any (ps.map Matrix.encode)) + 7 =
      8 * Nat.pair p.encode (Matrix.any ps).encode + 7
    rw [ih]

theorem project_calibration (i a : Nat) (shift : Int) (lower upper : Term) (p : Matrix) :
    Code.project (i, a, shift, lower.encode, upper.encode, p.encode) =
      (project i a shift lower upper p).encode := by
  unfold Code.project project
  rw [← any_calibration]
  apply congrArg WindowCode.any
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  exact WindowCodeProof.matrix_calibration i (replacement a lower shift d)
    (Matrix.conjunction (region i a shift lower upper) p)

theorem literalCodeCalibration : DominantBoundaryTargets.LiteralCodeCalibration :=
  ⟨center_calibration, project_calibration⟩

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
private theorem inverse_primitive : Primrec Code.inverse := unary_primitive 10 8
private theorem phi_primitive : Primrec WindowCode.phi := unary_primitive 10 6
private theorem var_primitive : Primrec WindowCode.var := unary_primitive 10 1
private theorem less_primitive : Primrec₂ WindowCode.less := binary_primitive 8 3
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

private theorem center_primitive : Primrec₂ Code.center :=
  add_primitive.comp
    (inverse_primitive.comp (divide_primitive.comp Primrec.fst
      (subtract_primitive.comp (multiply_primitive.comp (Primrec.const 2) Primrec.snd)
        (Primrec.const 10)))) (Primrec.const 10)

private theorem noWide_primitive : Primrec (fun q : Nat × (Nat × Nat) =>
    Code.noWide q.1 q.2.1 q.2.2) := by
  have ha : Primrec (fun q : Nat × (Nat × Nat) => q.1) := Primrec.fst
  have hl : Primrec (fun q : Nat × (Nat × Nat) => q.2.1) := Primrec.fst.comp Primrec.snd
  have hu : Primrec (fun q : Nat × (Nat × Nat) => q.2.2) := Primrec.snd.comp Primrec.snd
  exact less_primitive.comp (multiply_primitive.comp (Primrec.const 2) hu)
    (multiply_primitive.comp (Primrec.nat_mul.comp (Primrec.const 3) ha)
      (phi_primitive.comp (add_primitive.comp (center_primitive.comp ha hl) (Primrec.const 10))))

private abbrev RegionInput := Nat × (Nat × (Int × (Nat × Nat)))
private theorem region_primitive : Primrec (fun q : RegionInput =>
    Code.region q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hi : Primrec (fun q : RegionInput => q.1) := Primrec.fst
  have ha : Primrec (fun q : RegionInput => q.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun q : RegionInput => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun q : RegionInput => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hu : Primrec (fun q : RegionInput => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have harg : Primrec (fun q : RegionInput => WindowCode.shift (WindowCode.var q.1) q.2.2.1) :=
    shift_primitive.comp (var_primitive.comp hi) he
  have hdom : Primrec (fun q : RegionInput => WindowCode.domain (WindowCode.var q.1) q.2.2.1) :=
    negative_primitive.comp (less_primitive.comp (var_primitive.comp hi)
      (numeral_primitive.comp (toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp he))))
  have hwide : Primrec (fun q : RegionInput => Code.noWide q.2.1 q.2.2.2.1 q.2.2.2.2) :=
    noWide_primitive.comp (ha.pair (hl.pair hu))
  exact conjunction_primitive.comp hdom (conjunction_primitive.comp hwide
    (conjunction_primitive.comp
      (atMost_primitive.comp (multiply_primitive.comp (Primrec.const 2) hl)
        (multiply_primitive.comp (Primrec.nat_mul.comp (Primrec.const 3) ha) (phi_primitive.comp harg)))
      (atMost_primitive.comp (multiply_primitive.comp ha (phi_primitive.comp harg))
        (multiply_primitive.comp (Primrec.const 2) hu))))

private abbrev ReplacementInput := Nat × (Nat × (Int × Nat))
private theorem replacement_primitive : Primrec (fun q : ReplacementInput =>
    Code.replacement q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have ha : Primrec (fun q : ReplacementInput => q.1) := Primrec.fst
  have hl : Primrec (fun q : ReplacementInput => q.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun q : ReplacementInput => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun q : ReplacementInput => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact shift_primitive.comp
    (add_primitive.comp (subtract_primitive.comp (center_primitive.comp ha hl) (Primrec.const 20))
      (numeral_primitive.comp hd))
    (IntegerAlgorithms.Proof.negate_primitive.comp he)

attribute [local irreducible] Code.center Code.noWide Code.region Code.replacement

theorem actualNumericProgram : DominantBoundaryTargets.ActualNumericProgram := by
  let Q := Code.Input
  have hi : Primrec (fun q : Q => q.1) := Primrec.fst
  have ha : Primrec (fun q : Q => q.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun q : Q => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun q : Q => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hu : Primrec (fun q : Q => q.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hp : Primrec (fun q : Q => q.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hregion : Primrec (fun q : Q =>
      Code.region q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1) :=
    region_primitive.comp (hi.pair (ha.pair (he.pair (hl.pair hu))))
  have hguard : Primrec (fun q : Q => WindowCode.conjunction
      (Code.region q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1) q.2.2.2.2.2) :=
    conjunction_primitive.comp hregion hp
  have hrepl (d : Nat) : Primrec (fun q : Q =>
      Code.replacement q.2.1 q.2.2.2.1 q.2.2.1 d) :=
    replacement_primitive.comp (ha.pair (hl.pair (he.pair (Primrec.const d))))
  have hbranch (d : Nat) : Computable (fun q : Q =>
      WindowCode.matrixSubstitute q.1 (Code.replacement q.2.1 q.2.2.2.1 q.2.2.1 d)
        (WindowCode.conjunction (Code.region q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1) q.2.2.2.2.2)) :=
    WindowCodeProof.matrix_computable.comp (hguard.to_comp.pair (hi.to_comp.pair (hrepl d).to_comp))
  apply (disjunction_primitive.to_comp.comp (hbranch 0)
    (disjunction_primitive.to_comp.comp (hbranch 1)
      (disjunction_primitive.to_comp.comp (hbranch 2)
        (disjunction_primitive.to_comp.comp (hbranch 3)
          (disjunction_primitive.to_comp.comp (hbranch 4) (Computable.const 1)))))).of_eq
  intro q
  rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryProof
