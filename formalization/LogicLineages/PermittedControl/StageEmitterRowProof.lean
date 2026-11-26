module
public import LogicLineages.PermittedControl.StageEmitterRowTargets
import LogicLineages.PermittedControl.ActualRawCanonicalNodePrimitiveProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCodePrimitiveProof
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataPrimitiveProof
import LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapesPrimitiveProof
import LogicLineages.PermittedControl.ActualRawSignedCleanupPrimitiveProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetCodeProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

public section
namespace LogicLineages.PermittedControl.StageEmitter
open PreparedProjection (PreparedPacketCode)
open StageCallbackRawLevel
open ActualRawComparisonCeiling (LabelCode)
open ActualRawSignedStaticCeiling (RawSyntax)
open ActualBitFamilyRawLayout (RawBitRow)
open MixedSameRankResidue (WeightedCode)
open ActualCanonicalOperandGrouping (RawTerm groupRaw)
open ActualCanonicalOperandGroupingCode (groupRawPrimitive)
open ActualRawCanonicalNode (groupedPrimitive)
open ActualRawCanonicalNodeMetadata (labelsCode tapeHighestCode labelsPrimitive tapeHighestPrimitive)
open ActualRawCanonicalAnswerTapes (candidateTapes candidateTapesPrimitive)
open ActualRawSignedCleanup (cleanupCode cleanupPrimitive)
open ActualSyntaxChargeBudget (syntaxBudgetCode budgetCodeExact)

private theorem zeroTestPrimitive : Primrec (fun z : Int => decide (z = 0)) :=
  (Primrec.eq.comp Primrec.id (Primrec.const (0 : Int))).decide

private theorem nonnegativePrimitive : Primrec (fun z : Int => decide (0 ≤ z)) := by
  apply (Primrec.ite
    (Primrec.eq.comp OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof.sign_primitive
      (Primrec.const (-1 : Int)))
    (Primrec.const false) (Primrec.const true)).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem positivePrimitive : Primrec (fun z : Int => decide (0 < z)) := by
  apply ((Primrec.eq.comp OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof.sign_primitive
    (Primrec.const (1 : Int))).decide).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> simp
  | negSucc n => simp

private theorem signedBitPrimitive : Primrec (fun x : Nat × Int => signedBitCode x.1 x.2) := by
  have o : Primrec (fun x : Nat × Int => x.1) := Primrec.fst
  have c : Primrec (fun x : Nat × Int => x.2) := Primrec.snd
  have c0 : PrimrecPred (fun x : Nat × Int => x.1 = 0) := Primrec.eq.comp o (Primrec.const 0)
  have c1 : PrimrecPred (fun x : Nat × Int => x.1 = 1) := Primrec.eq.comp o (Primrec.const 1)
  have h := Primrec.ite c0 (zeroTestPrimitive.comp c)
    (Primrec.ite c1 (nonnegativePrimitive.comp c) (positivePrimitive.comp c))
  exact h.of_eq (fun x => rfl)

private theorem signedTipPrimitive :
    Primrec (fun x : Nat × Bool × Int => signedTipCode x.1 x.2.1 x.2.2) := by
  let A := Nat × Bool × Int
  have sel : Primrec (fun x : A => (x.1,x.2.2)) := Primrec.fst.pair (Primrec.snd.comp Primrec.snd)
  have bit : Primrec (fun x : A => signedBitCode x.1 x.2.2) := signedBitPrimitive.comp sel
  have b : Primrec (fun x : A => x.2.1) := Primrec.fst.comp Primrec.snd
  have pos : PrimrecPred (fun x : A => x.2.1 = true) := Primrec.eq.comp b (Primrec.const true)
  have inner := Primrec.ite pos bit (Primrec.not.comp bit)
  have test : PrimrecPred (fun x : A =>
      (if x.2.1 = true then signedBitCode x.1 x.2.2 else !(signedBitCode x.1 x.2.2)) = true) :=
    Primrec.eq.comp inner (Primrec.const true)
  have h := Primrec.ite test (Primrec.const (RawPacketAlgebra.encodePacket ([],.truth)))
    (Primrec.const (RawPacketAlgebra.encodePacket ([],.falsity)))
  exact h.of_eq (fun x => rfl)

private theorem nodePrimitive : Primrec (fun p : RawSyntax × List Nat => nodeOut p.1 p.2) := by
  let A := RawSyntax × List Nat
  have c : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have g : Primrec (fun p : A => groupRaw p.1.2) := groupRawPrimitive.comp (Primrec.snd.comp Primrec.fst)
  have t : Primrec (fun p : A => p.2) := Primrec.snd
  have sel : Primrec (fun p : A => (p.1.1,groupRaw p.1.2,p.2)) := c.pair (g.pair t)
  have h := groupedPrimitive.comp sel
  exact h

/-- The grouped labels of an entry's syntax. -/
private theorem entryLabelsPrimitive : Primrec (fun e : EntryCode => labelsCode (groupRaw e.2.2)) := by
  have s : Primrec (fun e : EntryCode => e.2.2) := Primrec.snd.comp Primrec.snd
  have h := labelsPrimitive.comp (groupRawPrimitive.comp s)
  exact h

section
variable (R : Rendering) (hR : RenderingEffective R)
include hR

private theorem stepPrimitive :
    Primrec (fun q : (Nat × EntryCode) × List Nat => stepOfCode R q.1.1 q.1.2 q.2) := by
  let Q := (Nat × EntryCode) × List Nat
  have top : Primrec (fun q : Q => q.1.1) := Primrec.fst.comp Primrec.fst
  have e : Primrec (fun q : Q => q.1.2) := Primrec.snd.comp Primrec.fst
  have tape : Primrec (fun q : Q => q.2) := Primrec.snd
  have syn : Primrec (fun q : Q => q.1.2.2) := Primrec.snd.comp e
  have guards : Primrec (fun q : Q => q.1.2.1) := Primrec.fst.comp e
  have node : Primrec (fun q : Q => nodeOut q.1.2.2 q.2) := nodePrimitive.comp (syn.pair tape)
  have labs : Primrec (fun q : Q => labelsCode (groupRaw q.1.2.2.2)) := entryLabelsPrimitive.comp e
  have guardQ : Primrec (fun q : Q => R.guard q.1.1 (labelsCode (groupRaw q.1.2.2.2)) q.2) := by
    have h := hR.guard.comp (top.pair (labs.pair tape))
    exact h
  have one : Primrec (fun q : Q => [R.guard q.1.1 (labelsCode (groupRaw q.1.2.2.2)) q.2]) :=
    Primrec.list_cons.comp guardQ (Primrec.const [])
  have app : Primrec (fun q : Q => q.1.2.1 ++ [R.guard q.1.1 (labelsCode (groupRaw q.1.2.2.2)) q.2]) :=
    Primrec.list_append.comp guards one
  have pairUp : Primrec (fun x : Q × RawSyntax =>
      (x.1.1.2.1 ++ [R.guard x.1.1.1 (labelsCode (groupRaw x.1.1.2.2.2)) x.1.2],x.2)) :=
    (app.comp Primrec.fst).pair Primrec.snd
  have mapped := Primrec.option_map (Primrec.snd.comp node) pairUp.to₂
  have coef : Primrec (fun q : Q => (nodeOut q.1.2.2 q.2).1) := Primrec.fst.comp node
  have zero : PrimrecPred (fun q : Q => (nodeOut q.1.2.2 q.2).1 = 0) :=
    Primrec.eq.comp coef (Primrec.const (0 : Int))
  have h := Primrec.ite zero mapped (Primrec.const (none : Option EntryCode))
  exact h.of_eq (fun q => rfl)

private theorem childrenPrimitive :
    Primrec (fun p : Nat × EntryCode => childrenCode R p.1 p.2) := by
  let P := Nat × EntryCode
  have top : Primrec (fun p : P => p.1) := Primrec.fst
  have grouped : Primrec (fun p : P => groupRaw p.2.2.2) :=
    groupRawPrimitive.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hi : Primrec (fun p : P => tapeHighestCode p.1 (groupRaw p.2.2.2)) := tapeHighestPrimitive.comp top grouped
  have active : PrimrecPred (fun p : P => tapeHighestCode p.1 (groupRaw p.2.2.2) = true) :=
    Primrec.eq.comp hi (Primrec.const true)
  have tapes : Primrec (fun p : P => candidateTapes (groupRaw p.2.2.2)) := candidateTapesPrimitive.comp grouped
  have kids := Primrec.listFilterMap tapes (stepPrimitive R hR).to₂
  have h := Primrec.ite active kids (Primrec.const ([] : List EntryCode))
  exact h.of_eq (fun p => rfl)

private theorem iterateLiteral (top : Nat) (start : RawSyntax) (n : Nat) :
    (n.rec [(([] : List PreparedPacketCode),start)]
      (fun _ acc => acc.flatMap (childrenCode R top)) : List EntryCode) = levelCode R top start n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.rec_add_one, ih, levelCode]

private theorem levelUncurried :
    Primrec (fun p : (Nat × RawSyntax) × Nat => levelCode R p.1.1 p.1.2 p.2) := by
  let A := (Nat × RawSyntax) × Nat
  let X := A × (Nat × List EntryCode)
  have fuel : Primrec (fun p : A => p.2) := Primrec.snd
  have st : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have entry : Primrec (fun p : A => (([] : List PreparedPacketCode),p.1.2)) :=
    (Primrec.const ([] : List PreparedPacketCode)).pair st
  have init : Primrec (fun p : A => [(([] : List PreparedPacketCode),p.1.2)]) :=
    Primrec.list_cons.comp entry (Primrec.const [])
  have sel : Primrec (fun y : X × EntryCode => (y.1.1.1.1,y.2)) :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd
  have kid0 := (childrenPrimitive R hR).comp sel
  have kid : Primrec₂ (fun (x : X) (e : EntryCode) => childrenCode R x.1.1.1 e) := kid0.to₂
  have acc : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have advance : Primrec (fun x : X => x.2.2.flatMap (childrenCode R x.1.1.1)) :=
    Primrec.list_flatMap acc kid
  have h := Primrec.nat_rec' fuel init advance.to₂
  exact h.of_eq (fun p => iterateLiteral R hR p.1.1 p.1.2 p.2)

private theorem appendPairPrimitive {α : Type} [Primcodable α] :
    Primrec₂ (fun (_ : α) (x : PreparedPacketCode × PreparedPacketCode) => R.append x.1 x.2) := by
  have a1 : Primrec (fun y : α × (PreparedPacketCode × PreparedPacketCode) => y.2.1) :=
    Primrec.fst.comp Primrec.snd
  have a2 : Primrec (fun y : α × (PreparedPacketCode × PreparedPacketCode) => y.2.2) :=
    Primrec.snd.comp Primrec.snd
  have h := hR.append.comp a1 a2
  exact h.to₂

private def leafList (q : ((Nat × Nat × Bool) × EntryCode) × List Nat) : List PreparedPacketCode :=
  q.1.2.1 ++ [R.guard q.1.1.1 (labelsCode (groupRaw q.1.2.2.2)) q.2]

private def leafTip (q : ((Nat × Nat × Bool) × EntryCode) × List Nat) : PreparedPacketCode :=
  signedTipCode q.1.1.2.1 q.1.1.2.2 (nodeOut q.1.2.2 q.2).1

private theorem leafListPrimitive : Primrec (leafList R) := by
  let Q := ((Nat × Nat × Bool) × EntryCode) × List Nat
  have top : Primrec (fun q : Q => q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have e : Primrec (fun q : Q => q.1.2) := Primrec.snd.comp Primrec.fst
  have tape : Primrec (fun q : Q => q.2) := Primrec.snd
  have guards : Primrec (fun q : Q => q.1.2.1) := Primrec.fst.comp e
  have labs : Primrec (fun q : Q => labelsCode (groupRaw q.1.2.2.2)) := entryLabelsPrimitive.comp e
  have args : Primrec (fun q : Q => (q.1.1.1,labelsCode (groupRaw q.1.2.2.2),q.2)) := top.pair (labs.pair tape)
  have guardQ : Primrec (fun q : Q => R.guard q.1.1.1 (labelsCode (groupRaw q.1.2.2.2)) q.2) := by
    have h := hR.guard.comp args
    exact h
  have one : Primrec (fun q : Q => [R.guard q.1.1.1 (labelsCode (groupRaw q.1.2.2.2)) q.2]) :=
    Primrec.list_cons.comp guardQ (Primrec.const [])
  have h := Primrec.list_append.comp guards one
  exact h

omit hR in
private theorem leafNodePrimitive :
    Primrec (fun q : ((Nat × Nat × Bool) × EntryCode) × List Nat => nodeOut q.1.2.2 q.2) := by
  let Q := ((Nat × Nat × Bool) × EntryCode) × List Nat
  have syn : Primrec (fun q : Q => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have tape : Primrec (fun q : Q => q.2) := Primrec.snd
  have h := nodePrimitive.comp (syn.pair tape)
  exact h

omit hR in
private theorem leafTipPrimitive : Primrec leafTip := by
  let Q := ((Nat × Nat × Bool) × EntryCode) × List Nat
  have cfg : Primrec (fun q : Q => q.1.1) := Primrec.fst.comp Primrec.fst
  have order : Primrec (fun q : Q => q.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp cfg)
  have positive : Primrec (fun q : Q => q.1.1.2.2) := Primrec.snd.comp (Primrec.snd.comp cfg)
  have coef : Primrec (fun q : Q => (nodeOut q.1.2.2 q.2).1) := Primrec.fst.comp leafNodePrimitive
  have args : Primrec (fun q : Q => (q.1.1.2.1,q.1.1.2.2,(nodeOut q.1.2.2 q.2).1)) :=
    order.pair (positive.pair coef)
  have h := signedTipPrimitive.comp args
  exact h

private theorem leafFoldPrimitive :
    Primrec (fun q : ((Nat × Nat × Bool) × EntryCode) × List Nat =>
      (leafList R q).foldr R.append (leafTip q)) := by
  have h := Primrec.list_foldr (leafListPrimitive R hR) leafTipPrimitive (appendPairPrimitive R hR)
  exact h

private theorem leafPrimitive :
    Primrec (fun q : ((Nat × Nat × Bool) × EntryCode) × List Nat =>
      leafOfCode R q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2 q.2) := by
  let Q := ((Nat × Nat × Bool) × EntryCode) × List Nat
  have coef : Primrec (fun q : Q => (nodeOut q.1.2.2 q.2).1) := Primrec.fst.comp leafNodePrimitive
  have zero : PrimrecPred (fun q : Q => (nodeOut q.1.2.2 q.2).1 = 0) :=
    Primrec.eq.comp coef (Primrec.const (0 : Int))
  have some' : Primrec (fun q : Q => some ((leafList R q).foldr R.append (leafTip q))) :=
    Primrec.option_some.comp (leafFoldPrimitive R hR)
  have h := Primrec.ite zero (Primrec.const (none : Option PreparedPacketCode)) some'
  apply h.of_eq
  intro q
  unfold leafOfCode leafList leafTip
  rfl

private theorem leavesPrimitive :
    Primrec (fun p : (Nat × Nat × Bool) × EntryCode => leavesCode R p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let P := (Nat × Nat × Bool) × EntryCode
  have top : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have order : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have positive : Primrec (fun p : P => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have guards : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have syn : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have grouped : Primrec (fun p : P => groupRaw p.2.2.2) := groupRawPrimitive.comp (Primrec.snd.comp syn)
  have hi : Primrec (fun p : P => tapeHighestCode p.1.1 (groupRaw p.2.2.2)) := tapeHighestPrimitive.comp top grouped
  have active : PrimrecPred (fun p : P => tapeHighestCode p.1.1 (groupRaw p.2.2.2) = true) :=
    Primrec.eq.comp hi (Primrec.const true)
  have tapes : Primrec (fun p : P => candidateTapes (groupRaw p.2.2.2)) := candidateTapesPrimitive.comp grouped
  have kids := Primrec.listFilterMap tapes (leafPrimitive R hR).to₂
  have linArgs : Primrec (fun p : P => (p.1.1,p.2.2,p.1.2.1,p.1.2.2)) :=
    top.pair (syn.pair (order.pair positive))
  have lin : Primrec (fun p : P => R.linear p.1.1 p.2.2 p.1.2.1 p.1.2.2) := by
    have h := hR.linear.comp linArgs
    exact h
  have fold := Primrec.list_foldr guards lin (appendPairPrimitive R hR)
  have other := Primrec.list_cons.comp fold (Primrec.const ([] : List PreparedPacketCode))
  have h := Primrec.ite active kids other
  exact h.of_eq (fun p => rfl)

private theorem signedPrimitive :
    Primrec (fun p : Nat × Nat × Bool × Nat × RawSyntax =>
      signedCode R p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let P := Nat × Nat × Bool × Nat × RawSyntax
  have top : Primrec (fun p : P => p.1) := Primrec.fst
  have order : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have positive : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have fuel : Primrec (fun p : P => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have syn : Primrec (fun p : P => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have indices : Primrec (fun p : P => List.range (p.2.2.2.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp fuel)
  have levArgs : Primrec (fun x : P × Nat => ((x.1.1,x.1.2.2.2.2),x.2)) :=
    ((top.comp Primrec.fst).pair (syn.comp Primrec.fst)).pair Primrec.snd
  have lev : Primrec (fun x : P × Nat => levelCode R x.1.1 x.1.2.2.2.2 x.2) := by
    have h := (levelUncurried R hR).comp levArgs
    exact h
  have cfg : Primrec (fun y : (P × Nat) × EntryCode => ((y.1.1.1,y.1.1.2.1,y.1.1.2.2.1),y.2)) :=
    (((top.comp Primrec.fst).comp Primrec.fst).pair
      (((order.comp Primrec.fst).comp Primrec.fst).pair ((positive.comp Primrec.fst).comp Primrec.fst))).pair
      Primrec.snd
  have leaf0 : Primrec (fun y : (P × Nat) × EntryCode => leavesCode R y.1.1.1 y.1.1.2.1 y.1.1.2.2.1 y.2) := by
    have h := (leavesPrimitive R hR).comp cfg
    exact h
  have inner := Primrec.list_flatMap lev leaf0.to₂
  have h := Primrec.list_flatMap indices inner.to₂
  exact h.of_eq (fun p => rfl)

private theorem rowPrimitive :
    Primrec (fun p : Nat × Nat × RawBitRow => rowCode R p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × RawBitRow
  have width : Primrec (fun p : P => p.1) := Primrec.fst
  have top : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have row : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have tag : Primrec (fun p : P => p.2.2.1.1.1) := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp row))
  have modulus : Primrec (fun p : P => p.2.2.1.1.2) := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp row))
  have syn : Primrec (fun p : P => p.2.2.1.2) := Primrec.snd.comp (Primrec.fst.comp row)
  have pos : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp row
  have modArgs : Primrec (fun p : P => (p.2.1,p.2.2.1.1.2,p.2.2.1.2,p.2.2.2)) :=
    top.pair (modulus.pair (syn.pair pos))
  have modOne : Primrec (fun p : P => R.modular p.2.1 p.2.2.1.1.2 p.2.2.1.2 p.2.2.2) := by
    have h := hR.modular.comp modArgs
    exact h
  have modBranch : Primrec (fun p : P => [R.modular p.2.1 p.2.2.1.1.2 p.2.2.1.2 p.2.2.2]) :=
    Primrec.list_cons.comp modOne (Primrec.const ([] : List PreparedPacketCode))
  have clean : Primrec (fun p : P => cleanupCode p.2.2.1.2) := cleanupPrimitive.comp syn
  have budget : Primrec (fun p : P => syntaxBudgetCode p.1 (cleanupCode p.2.2.1.2).2) := by
    have h := budgetCodeExact.1.comp width (Primrec.snd.comp clean)
    exact h
  have sArgs : Primrec (fun p : P =>
      (p.2.1,p.2.2.1.1.1,p.2.2.2,syntaxBudgetCode p.1 (cleanupCode p.2.2.1.2).2,cleanupCode p.2.2.1.2)) :=
    top.pair (tag.pair (pos.pair (budget.pair clean)))
  have signedBranch : Primrec (fun p : P => signedCode R p.2.1 p.2.2.1.1.1 p.2.2.2
      (syntaxBudgetCode p.1 (cleanupCode p.2.2.1.2).2) (cleanupCode p.2.2.1.2)) := by
    have h := (signedPrimitive R hR).comp sArgs
    exact h
  have three : PrimrecPred (fun p : P => p.2.2.1.1.1 = 3) := Primrec.eq.comp tag (Primrec.const 3)
  have h := Primrec.ite three modBranch signedBranch
  exact h.of_eq (fun p => rfl)

end

theorem exactLevelCodeEffectivity : ExactLevelCodeEffectivity :=
  fun R hR => levelUncurried R hR

theorem exactSignedCodeEffectivity : ExactSignedCodeEffectivity :=
  fun R hR => signedPrimitive R hR

theorem exactRowCodeEffectivity : ExactRowCodeEffectivity :=
  fun R hR => rowPrimitive R hR

theorem fullStageEmitterRow : FullStageEmitterRow :=
  ⟨exactLevelCodeEffectivity,exactSignedCodeEffectivity,exactRowCodeEffectivity⟩

#print axioms exactRowCodeEffectivity
#print axioms fullStageEmitterRow
end LogicLineages.PermittedControl.StageEmitter
