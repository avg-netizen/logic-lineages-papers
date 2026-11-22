module
public import LogicLineages.PermittedControl.MixedSameRankResidueTargets
import LogicLineages.PermittedControl.OrdinaryResidueOperandStatementChecks
import LogicLineages.PermittedControl.CountCongruenceNamedRowCodeStatementChecks
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.MixedSameRankResidue
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open StatementChecks (fixed_ordinaryResidueOperandCodeExact fixed_countCongruenceNamedRowCodeExact)

private theorem countPrimitive :
    Primrec (fun p : Nat × Nat × Nat => CountCongruenceNamedRow.residueCount p.1 p.2.1 p.2.2) := by
  let Arg := Nat × Nat × Nat
  have gap : Primrec (fun p : Arg => p.1) := Primrec.fst
  have norm : Primrec (fun p : Arg => p.2.1) := Primrec.fst.comp Primrec.snd
  have j : Primrec (fun p : Arg => p.2.2) := Primrec.snd.comp Primrec.snd
  have half := ofNat_primitive.comp (Primrec.nat_div.comp j (Primrec.const 2))
  have ceiling := ofNat_primitive.comp (Primrec.nat_div.comp (Primrec.succ.comp norm) (Primrec.const 2))
  have delta : Primrec (fun p : Arg => ((p.2.2/2 : Nat) : Int) - (((p.2.1+1)/2 : Nat) : Int)) := by
    simpa only [sub_eq_add_neg] using add_primitive.comp half (negate_primitive.comp ceiling)
  exact Primrec.ite (Primrec.eq.comp gap (Primrec.const 0)) delta (ofNat_primitive.comp gap)

private theorem operandPrimitive : Primrec₂ operandResidueCode := by
  let Arg := LowerOperandCode × Nat
  have op : Primrec (Prod.fst : Arg → LowerOperandCode) := Primrec.fst
  have j : Primrec (Prod.snd : Arg → Nat) := Primrec.snd
  have tag := Primrec.fst.comp op
  have field := Primrec.snd.comp (Primrec.snd.comp op)
  have endpoints := Primrec.snd.comp (Primrec.snd.comp field)
  have lam := Primrec.fst.comp endpoints
  have mu := Primrec.snd.comp endpoints
  have k := shortFieldPreprocessingEffective.2.1.comp lam mu
  have norm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp mu
  have count := countPrimitive.comp (k.pair (norm.pair j))
  have ordinary := fixed_ordinaryResidueOperandCodeExact.1.comp field j
  exact (Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) (ofNat_primitive.comp j)
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) ordinary count)).to₂

private theorem operandTailPrimitive :
    Primrec (fun p : Nat × Nat × LowerOperandCode => operandTailCode p.1 p.2.1 p.2.2) := by
  let Arg := Nat × Nat × LowerOperandCode
  have B : Primrec (fun p : Arg => p.1) := Primrec.fst
  have m : Primrec (fun p : Arg => p.2.1) := Primrec.fst.comp Primrec.snd
  have op : Primrec (fun p : Arg => p.2.2) := Primrec.snd.comp Primrec.snd
  have tag := Primrec.fst.comp op
  have field := Primrec.snd.comp (Primrec.snd.comp op)
  have endpoints := Primrec.snd.comp (Primrec.snd.comp field)
  have lam := Primrec.fst.comp endpoints
  have mu := Primrec.snd.comp endpoints
  have count := fixed_countCongruenceNamedRowCodeExact.2.1.comp (B.pair (lam.pair (mu.pair m)))
  have ordinary := fixed_ordinaryResidueOperandCodeExact.2.1.comp (B.pair (m.pair field))
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) ordinary count)

private theorem weightedPrimitive : Primrec₂ weightedResidueCode := by
  let Arg := List WeightedCode × Nat
  let Step := Arg × (WeightedCode × Int)
  have xs : Primrec (Prod.fst : Arg → List WeightedCode) := Primrec.fst
  have j : Primrec (fun p : Step => p.1.2) := Primrec.snd.comp Primrec.fst
  have term : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have signed := mul_primitive.comp (Primrec.fst.comp term)
    (operandPrimitive.comp (Primrec.snd.comp term) j)
  have step := add_primitive.comp signed acc
  exact (Primrec.list_foldr xs (Primrec.const (0 : Int)) step.to₂).to₂

private theorem weightedTailPrimitive :
    Primrec (fun p : Nat × Nat × List WeightedCode => weightedTailCode p.1 p.2.1 p.2.2) := by
  let Arg := Nat × Nat × List WeightedCode
  let Step := Arg × (WeightedCode × Nat)
  have xs : Primrec (fun p : Arg => p.2.2) := Primrec.snd.comp Primrec.snd
  have B : Primrec (fun p : Step => p.1.1) := Primrec.fst.comp Primrec.fst
  have m : Primrec (fun p : Step => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have op : Primrec (fun p : Step => p.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have acc : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have step := Primrec.nat_max.comp (operandTailPrimitive.comp (B.pair (m.pair op))) acc
  exact Primrec.list_foldr xs (Primrec.const 0) step.to₂

private theorem operandLiteral (op : LowerOperand) (j : Nat) :
    operandResidueCode op.code j = operandResidue j op := by
  cases op with
  | coordinate rank => rfl
  | ordinary rank F => exact fixed_ordinaryResidueOperandCodeExact.2.2.1 F j
  | count rank lam mu =>
    simp [operandResidueCode,operandResidue,LowerOperand.code,longFieldCode,shortGapLength,normal_norm_code]

private theorem operandTailLiteral (B m : Nat) (op : LowerOperand) :
    operandTailCode B m op.code = operandTail B m op := by
  cases op with
  | coordinate rank => rfl
  | ordinary rank F => exact fixed_ordinaryResidueOperandCodeExact.2.2.2 B m F
  | count rank lam mu => exact fixed_countCongruenceNamedRowCodeExact.2.2.2.1 B m lam mu

private theorem weightedLiteral (terms : List WeightedOperand) (j : Nat) :
    weightedResidueCode (terms.map encodeWeighted) j = weightedResidue terms j := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    change t.1 * operandResidueCode t.2.code j + weightedResidueCode (terms.map encodeWeighted) j =
      t.1 * operandResidue j t.2 + weightedResidue terms j
    rw [operandLiteral,ih]

theorem weightedTailLiteral (B m : Nat) (terms : List WeightedOperand) :
    weightedTailCode B m (terms.map encodeWeighted) = weightedTail B m terms := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    change max (operandTailCode B m t.2.code) (weightedTailCode B m (terms.map encodeWeighted)) =
      max (operandTail B m t.2) (weightedTail B m terms)
    rw [operandTailLiteral,ih]

theorem codeExact : CodeExact :=
  ⟨weightedPrimitive,weightedTailPrimitive,weightedLiteral,weightedTailLiteral⟩

end LogicLineages.PermittedControl.MixedSameRankResidue
