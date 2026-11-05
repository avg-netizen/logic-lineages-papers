module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsCodeProof
open NestedRows
attribute [local irreducible] Nat.sqrt Nat.unpair
  SignedRows.Code.substitute SignedRows.Code.anchorDomain

private theorem binary_primitive (tag : Nat) :
    Primrec₂ (fun a b : Nat => 6 * Nat.pair a b + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair)
    (Primrec.const tag)
private theorem unary_primitive (tag : Nat) :
    Primrec (fun a : Nat => 6 * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id)
    (Primrec.const tag)
private theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp IntegerAlgorithms.Proof.sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) IntegerAlgorithms.Proof.abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

theorem substitute_primitive :
    Primrec₂ (fun args : Code.Input => Code.substitute args.1.1 args.1.2 args.2.1 args.2.2) := by
  let A := Code.Input × Nat
  have hi : Primrec (fun p : A => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hj : Primrec (fun p : A => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun p : A => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hb : Primrec (fun p : A => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hdom : Primrec (fun p : A => SignedRows.Code.anchorDomain p.1.1.2 p.1.2.1) :=
    SignedRowsCodeProof.anchorDomain_primitive.comp hj ha
  have hhigh : Primrec (fun p : A =>
      SignedRows.Code.substitute p.1.1.1 p.1.1.2 (p.1.2.1 + p.1.2.2) p.2) :=
    SignedRowsCodeProof.substitute_primitive.comp
      ((hi.pair hj).pair (IntegerAlgorithms.Proof.add_primitive.comp ha hb)) Primrec.snd
  have hlow : Primrec (fun p : A => BoundedRows.Code.formula p.1.1.1 p.1.2.2.toNat p.2) :=
    BoundedRowsCodeProof.formula_primitive.comp
      (hi.pair (toNat_primitive.comp hb)) Primrec.snd
  exact (binary_primitive 5).comp ((binary_primitive 4).comp hdom hhigh)
    ((binary_primitive 4).comp ((unary_primitive 3).comp hdom) hlow)

theorem actualNumericPrograms : NestedRowsTargets.ActualNumericPrograms :=
  substitute_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsCodeProof
