module
public import LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRowsTargets
import LogicLineages.OrdinalComparison.RawSplitProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.EncodedDescentProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRows
open OrdinalComparison
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof (ofNat_primitive negate_primitive)
open HeterogeneousSignedMatrixSlice (RawRow TestCode)
open PreparedProjection (LowerOperandCode)
open MixedSameRankResidue (WeightedCode)
open NaturalAffineGateGraph (Expression)
open OriginalPrintedCircuitNumericRead (RawGate)

private theorem coordPrimitive : Primrec coordinateCode :=
  (Primrec.const 0).pair (Primrec.id.pair (Primrec.const (0,0,0,0)))

private theorem weightedPrimitive : Primrec weightedCoord :=
  Primrec.fst.pair (coordPrimitive.comp Primrec.snd)

private theorem affinePrimitive : Primrec affineEqualityCode := by
  have c : Primrec (fun p : AffineArgs => p.1.1) := Primrec.fst.comp Primrec.fst
  have tape : Primrec (fun p : AffineArgs => p.1.2) := Primrec.snd.comp Primrec.fst
  have term : Primrec (fun p : AffineArgs × (Int × Nat) => weightedCoord p.2) :=
    weightedPrimitive.comp Primrec.snd
  have out : Primrec (fun p : AffineArgs => ((-1,coordinateCode p.2) : WeightedCode)) :=
    (Primrec.const (-1)).pair (coordPrimitive.comp Primrec.snd)
  exact (Primrec.const ((0,0) : TestCode)).pair
    (c.pair (Primrec.list_cons.comp out (Primrec.list_map tape term.to₂)))

private theorem normPrimitive : Primrec rawNormCode :=
  Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive

private theorem guardPrimitive : Primrec₂ normGuardCode := by
  have c : Primrec (fun p : Nat × Nat => -(rawNormCode p.1 : Int)) :=
    negate_primitive.comp (ofNat_primitive.comp (normPrimitive.comp Primrec.fst))
  have t : Primrec (fun p : Nat × Nat => ((1,coordinateCode p.2) : WeightedCode)) :=
    (Primrec.const 1).pair (coordPrimitive.comp Primrec.snd)
  have raw : Primrec (fun p : Nat × Nat => normGuardCode p.1 p.2) :=
    (Primrec.const ((1,0) : TestCode)).pair (c.pair (Primrec.list_cons.comp t (Primrec.const [])))
  exact raw.to₂

private theorem collapseEqualityPrimitive :
    Primrec (fun p : Nat × Nat × Nat => collapseEqualityCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Nat
  have head : Primrec (fun p : A => p.1) := Primrec.fst
  have slot : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have output : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have lower (tag : Nat) : Primrec (fun p : A =>
      ((1,(tag,p.2.1,(1,0,p.1,zeroCode))) : WeightedCode)) :=
    (Primrec.const 1).pair ((Primrec.const tag).pair (slot.pair
      ((Primrec.const 1).pair ((Primrec.const 0).pair (head.pair (Primrec.const zeroCode))))))
  have out : Primrec (fun p : A => ((-1,coordinateCode p.2.2) : WeightedCode)) :=
    (Primrec.const (-1)).pair (coordPrimitive.comp output)
  exact (Primrec.const ((0,0) : TestCode)).pair ((Primrec.const 0).pair
    (Primrec.list_cons.comp out (Primrec.list_cons.comp (lower 1)
      (Primrec.list_cons.comp (lower 2) (Primrec.const [])))))

private theorem limitPrimitive : Primrec limitRowsCode := by
  have head : Primrec (fun p : LimitArgs => p.1) := Primrec.fst
  have exp : Primrec (fun p : LimitArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have slot : Primrec (fun p : LimitArgs => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have output : Primrec (fun p : LimitArgs => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_cons.comp (affinePrimitive.comp (exp.pair slot))
    (Primrec.list_cons.comp (guardPrimitive.comp head slot)
      (Primrec.list_cons.comp (collapseEqualityPrimitive.comp (head.pair (slot.pair output)))
        (Primrec.const [])))

private theorem collapsePrimitive : Primrec collapseRowsCode := by
  have head : Primrec (fun p : CollapseArgs => p.1) := Primrec.fst
  have source : Primrec (fun p : CollapseArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have slot : Primrec (fun p : CollapseArgs => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have output : Primrec (fun p : CollapseArgs => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have guard := encodedFiniteAlgorithmsPrimitiveRecursive.1.comp head
  have value := (Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2).comp head
  have split := Primrec.unpair.comp ((Primrec.nat_iff.mpr rawSplitPrimitiveRecursive).comp head)
  have limit : Primrec (fun p : CollapseArgs => (rawSplitCode p.1).unpair.1) :=
    Primrec.fst.comp split
  have shift : Primrec (fun p : CollapseArgs => rawNormCode (rawSplitCode p.1).unpair.1 +
      (rawSplitCode p.1).unpair.2) :=
    Primrec.nat_add.comp (normPrimitive.comp limit) (Primrec.snd.comp split)
  have coeffs : Primrec (fun p : CollapseArgs => ([(1,p.2.1)] : List (Int × Nat))) :=
    Primrec.list_cons.comp ((Primrec.const 1).pair source) (Primrec.const [])
  have finite := (ofNat_primitive.comp value).pair coeffs
  have shifted := (ofNat_primitive.comp shift).pair coeffs
  have fromFinite : Primrec (fun p : CollapseArgs =>
      [affineEqualityCode (((encodedFiniteValue p.1 : Int),[(1,p.2.1)]),p.2.2.2)]) :=
    Primrec.list_cons.comp (affinePrimitive.comp (finite.pair output)) (Primrec.const [])
  have fromLimit : Primrec (fun p : CollapseArgs => limitRowsCode
      ((rawSplitCode p.1).unpair.1,
        ((rawNormCode (rawSplitCode p.1).unpair.1 + (rawSplitCode p.1).unpair.2 : Nat),[(1,p.2.1)]),
         p.2.2.1,p.2.2.2)) :=
    limitPrimitive.comp (limit.pair (shifted.pair (slot.pair output)))
  apply (Primrec.cond guard fromFinite fromLimit).of_eq
  intro p
  cases h : encodedFiniteTest p.1 <;> simp [collapseRowsCode,h]

private theorem stepPrimitive : Primrec stepCode := by
  have n : Primrec (fun p : StepArgs => p.1) := Primrec.fst
  have gate : Primrec (Prod.snd : StepArgs → RawGate) := Primrec.snd
  have tag : Primrec (fun p : StepArgs => p.2.1) := Primrec.fst.comp gate
  have src : Primrec (fun p : StepArgs => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp gate)
  have suffix : Primrec (fun p : StepArgs => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp gate)
  have output : Primrec (fun p : StepArgs => p.2.2.2.1) := Primrec.fst.comp suffix
  have rest : Primrec (fun p : StepArgs => p.2.2.2.2) := Primrec.snd.comp suffix
  have spec : Primrec (fun p : StepArgs => p.2.2.2.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp rest)
  have exp : Primrec (fun p : StepArgs => p.2.2.2.2.2) := Primrec.snd.comp rest
  have affine := Primrec.list_cons.comp (affinePrimitive.comp (exp.pair output)) (Primrec.const [])
  have collapse := collapsePrimitive.comp (spec.pair (src.pair (n.pair output)))
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0))
    (Primrec.option_some.comp (n.pair affine))
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1))
      (Primrec.option_some.comp ((Primrec.succ.comp n).pair collapse)) (Primrec.const none))

theorem exactOriginalRawBaseGateEffectivity : ExactOriginalRawBaseGateEffectivity :=
  ⟨affinePrimitive,limitPrimitive,collapsePrimitive,stepPrimitive⟩

end LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRows
