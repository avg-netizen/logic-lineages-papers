module
public import LogicLineages.PermittedControl.OrdinaryResidueOperandTargets
import LogicLineages.PermittedControl.CountCongruenceNamedRowCodeStatementChecks
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OrdinaryResidueOperand
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open StatementChecks (fixed_countCongruenceNamedRowCodeExact)

private theorem differencePrimitive :
    Primrec₂ (fun (q a : Nat) => 2 * (q : Int) - 2 * (a : Int)) := by
  let Arg := Nat × Nat
  have q : Primrec (Prod.fst : Arg → Nat) := Primrec.fst
  have a : Primrec (Prod.snd : Arg → Nat) := Primrec.snd
  have left := mul_primitive.comp (Primrec.const (2 : Int)) (ofNat_primitive.comp q)
  have right := mul_primitive.comp (Primrec.const (2 : Int)) (ofNat_primitive.comp a)
  simpa only [sub_eq_add_neg] using (add_primitive.comp left (negate_primitive.comp right)).to₂

private theorem floorPrimitive : Primrec₂ doubledFloor :=
  differencePrimitive.comp
    (Primrec.nat_div.comp (Primrec.fst : Primrec (Prod.fst : Nat × Nat → Nat)) (Primrec.const 2))
    Primrec.snd

private theorem ceilingPrimitive : Primrec₂ doubledCeiling :=
  differencePrimitive.comp
    (Primrec.nat_div.comp (Primrec.succ.comp
      (Primrec.fst : Primrec (Prod.fst : Nat × Nat → Nat))) (Primrec.const 2))
    Primrec.snd

private theorem residuePrimitive : Primrec₂ residueCode := by
  let Arg := LongFieldCode × Nat
  have field : Primrec (Prod.fst : Arg → LongFieldCode) := Primrec.fst
  have j : Primrec (Prod.snd : Arg → Nat) := Primrec.snd
  have tag := Primrec.fst.comp field
  have parameters := Primrec.snd.comp field
  have a := Primrec.fst.comp parameters
  have lam := Primrec.fst.comp (Primrec.snd.comp parameters)
  have mu := Primrec.snd.comp (Primrec.snd.comp parameters)
  have gap := shortFieldPreprocessingEffective.2.1.comp lam mu
  have norm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp mu
  have ident := Primrec.ite (Primrec.eq.comp a (Primrec.const 0))
    (ofNat_primitive.comp j) (floorPrimitive.comp j a)
  have entry := Primrec.ite (Primrec.eq.comp gap (Primrec.const 0))
    (ceilingPrimitive.comp norm a) (floorPrimitive.comp j (Primrec.nat_add.comp gap a))
  exact (Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) ident entry).to₂

private theorem tailPrimitive :
    Primrec (fun p : Nat × Nat × LongFieldCode => residueTailCode p.1 p.2.1 p.2.2) := by
  let Arg := Nat × Nat × LongFieldCode
  have B : Primrec (Prod.fst : Arg → Nat) := Primrec.fst
  have m : Primrec (fun p : Arg => p.2.1) := Primrec.fst.comp Primrec.snd
  have field : Primrec (fun p : Arg => p.2.2) := Primrec.snd.comp Primrec.snd
  have tag := Primrec.fst.comp field
  have parameters := Primrec.snd.comp field
  have a := Primrec.fst.comp parameters
  have lam := Primrec.fst.comp (Primrec.snd.comp parameters)
  have mu := Primrec.snd.comp (Primrec.snd.comp parameters)
  have entry := fixed_countCongruenceNamedRowCodeExact.2.1.comp
    (B.pair (lam.pair (mu.pair m)))
  have iter := Primrec.ite (Primrec.eq.comp a (Primrec.const 0))
    (Primrec.const 0) (Primrec.nat_max.comp m B)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) iter entry

private theorem residueLiteral (F : ValueField) (j : Nat) :
    residueCode (longFieldCode F) j = residue F j := by
  cases F with
  | iterate a => cases a <;> simp [longFieldCode,residueCode,residue]
  | entry a lam mu =>
    simp [longFieldCode,residueCode,residue,shortGapLength,normal_norm_code]

theorem tailLiteral (B m : Nat) (F : ValueField) :
    residueTailCode B m (longFieldCode F) = residueTail B m F := by
  cases F with
  | iterate a => cases a <;> simp [longFieldCode,residueTailCode,residueTail]
  | entry a lam mu =>
    simpa only [longFieldCode,residueTailCode,residueTail,Nat.one_ne_zero,if_false] using
      fixed_countCongruenceNamedRowCodeExact.2.2.2.1 B m lam mu

theorem codeExact : CodeExact :=
  ⟨residuePrimitive,tailPrimitive,residueLiteral,tailLiteral⟩

end LogicLineages.PermittedControl.OrdinaryResidueOperand
