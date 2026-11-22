module
public import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorTargets
import LogicLineages.PermittedControl.OrdinalEndpointProgramsProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
open OrdinalComparison OrdinalComparison.LayeredComparison
open MixedSameRankResidue ConcreteCountPairReplacement

private theorem leastStepPrimitive : Primrec₂ leastStepCode := by
  let A := PrefixCode × Option PrefixCode
  let P := A × PrefixCode
  have hd : Primrec (Prod.fst : A → PrefixCode) := Primrec.fst
  have left : Primrec (fun p : P => p.1.1) := hd.comp Primrec.fst
  have right : Primrec (Prod.snd : P → PrefixCode) := Primrec.snd
  have prefer : PrimrecPred (fun p : P => p.1.1.1 ≤ p.2.1) :=
    Primrec.nat_le.comp (Primrec.fst.comp left) (Primrec.fst.comp right)
  have someLeft := Primrec.option_some.comp left
  have someRight := Primrec.option_some.comp right
  have body := Primrec.ite prefer someLeft someRight
  have packed := Primrec.option_casesOn (Primrec.snd : Primrec (Prod.snd : A → Option PrefixCode))
    (Primrec.option_some.comp hd) body.to₂
  apply packed.to₂.of_eq
  intro p q
  cases q <;> rfl

theorem leastPrimitive : Primrec leastCode := by
  let A := List PrefixCode × (PrefixCode × Option PrefixCode)
  have step : Primrec (fun p : A => leastStepCode p.2.1 p.2.2) :=
    leastStepPrimitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.id (Primrec.const (none : Option PrefixCode)) step.to₂

private theorem anchorPrimitive : Primrec₂ anchorCode := by
  let A := PrefixCode × Int
  have rank : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have lam : Primrec (fun p : A => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have eta : Primrec (fun p : A => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have key := (Primrec.const 2).pair (rank.pair ((Primrec.const 1).pair ((Primrec.const 0).pair (lam.pair eta))))
  exact ((Primrec.snd : Primrec (Prod.snd : A → Int)).pair key).to₂

private theorem replacementPrimitive : Primrec₂ replacementCode := by
  let A := Nat × IntervalPairCodes
  have hp : Primrec (fun z : A => z.2.1) := Primrec.fst.comp Primrec.snd
  have hq : Primrec (fun z : A => z.2.2) := Primrec.snd.comp Primrec.snd
  have hd := ordinalSubCodeEffective.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp)
  have hk := ordinalAddCodeEffective.comp (Primrec.snd.comp hq) hd
  exact ((Primrec.const 2).pair (Primrec.fst.pair
    ((Primrec.const 1).pair ((Primrec.const 0).pair ((Primrec.fst.comp hq).pair hk))))).to₂

private theorem moveOnePrimitive : Primrec₂ moveOneCode := by
  let A := PrefixCode × PrefixCode
  have a : Primrec (Prod.fst : A → PrefixCode) := Primrec.fst
  have p : Primrec (Prod.snd : A → PrefixCode) := Primrec.snd
  have rank : Primrec (Prod.fst : PrefixCode → Nat) := Primrec.fst
  have lam : Primrec (fun q : PrefixCode => q.2.1) := Primrec.fst.comp Primrec.snd
  have eta : Primrec (fun q : PrefixCode => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have w : Primrec (fun q : A => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp p))
  have ends := lam.pair eta
  have bare := anchorPrimitive.comp a w
  have H := replacementPrimitive.comp (rank.comp a) ((ends.comp p).pair (ends.comp a))
  have pair := (IntegerAlgorithms.Proof.negate_primitive.comp w).pair H
  have single := Primrec.list_cons.comp bare (Primrec.const ([] : List WeightedCode))
  have both := Primrec.list_cons.comp bare (Primrec.list_cons.comp pair (Primrec.const []))
  exact (Primrec.ite (Primrec.eq.comp (rank.comp p) (rank.comp a)) single both).to₂

theorem movedPrimitive : Primrec₂ movedCode := by
  let A := Option PrefixCode × List PrefixCode
  let P := A × PrefixCode
  let Q := P × PrefixCode
  have tape : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have best : Primrec (fun p : Q => p.1.2) := Primrec.snd.comp Primrec.fst
  have item : Primrec (Prod.snd : Q → PrefixCode) := Primrec.snd
  have step : Primrec (fun p : Q => moveOneCode p.1.2 p.2) := moveOnePrimitive.comp best item
  have series : Primrec (fun p : P => p.1.2.flatMap (moveOneCode p.2)) :=
    Primrec.list_flatMap tape step.to₂
  have commit := Primrec.option_casesOn (Primrec.fst : Primrec (Prod.fst : A → Option PrefixCode))
    (Primrec.const ([] : List WeightedCode)) series.to₂
  apply commit.to₂.of_eq
  intro a ps
  cases a <;> rfl

end LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
