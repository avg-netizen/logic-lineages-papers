module
public import LogicLineages.PermittedControl.ActualRawMixedFamilyCeilingTargets
import LogicLineages.PermittedControl.ActualRawSignedCleanupPrimitiveProof
import LogicLineages.PermittedControl.ActualRawSignedStaticCeilingPrimitiveProof
import LogicLineages.PermittedControl.ActualBitFamilyRawReadCeilingPrimitiveProof
import LogicLineages.PermittedControl.MixedSameRankResidueCodeProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMixedFamilyCeiling
open MixedSameRankResidue (WeightedCode weightedTailCode)
open ActualRawSignedStaticCeiling (RawSyntax staticCode staticPrimitive)
open ActualRawSignedCleanup (cleanupCode cleanupPrimitive)
open ActualBitFamilyRawReadCeiling (rowCode rowPrimitive)
open ActualBitFamilyRawLayout (RawBitRow RawFamily)
open HeterogeneousSignedMatrixSlice (RawRow TestCode)

private theorem signedFromSyntax :
    Primrec (fun p : Nat × Nat × RawSyntax => staticCode p.1 p.2.1 (cleanupCode p.2.2)) := by
  let A := Nat × Nat × RawSyntax
  have cfg : Primrec (Prod.fst : A → Nat) := Primrec.fst
  have width : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have src : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact staticPrimitive.comp (cfg.pair (width.pair (cleanupPrimitive.comp src)))

private theorem modularFromRow :
    Primrec (fun p : Nat × RawRow => weightedTailCode p.1 p.2.1.2 p.2.2.2) := by
  let A := Nat × RawRow
  have cfg : Primrec (Prod.fst : A → Nat) := Primrec.fst
  have header : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have source : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have modulus : Primrec (fun p : A => p.2.1.2) := Primrec.snd.comp header
  have terms : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp source
  exact MixedSameRankResidue.codeExact.2.1.comp (cfg.pair (modulus.pair terms))

private abbrev RawCostArgs := Nat × Nat × RawBitRow

private theorem sourceRowPrimitive : Primrec (fun p : RawCostArgs => p.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem tagPrimitive : Primrec (fun p : RawCostArgs => p.2.2.1.1.1) :=
  Primrec.fst.comp (Primrec.fst.comp sourceRowPrimitive)

private theorem signedFromBit :
    Primrec (fun p : RawCostArgs => staticCode p.1 p.2.1 (cleanupCode p.2.2.1.2)) := by
  have cfg : Primrec (Prod.fst : RawCostArgs → Nat) := Primrec.fst
  have width : Primrec (fun p : RawCostArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have src : Primrec (fun p : RawCostArgs => p.2.2.1.2) := Primrec.snd.comp sourceRowPrimitive
  exact signedFromSyntax.comp (cfg.pair (width.pair src))

private theorem modularFromBit :
    Primrec (fun p : RawCostArgs => weightedTailCode p.1 p.2.2.1.1.2 p.2.2.1.2.2) :=
  modularFromRow.comp (Primrec.fst.pair sourceRowPrimitive)

private theorem maxReadAndCost {A : Type} [Primcodable A]
    {reads signed modular testTag : A → Nat}
    (hRead : Primrec reads) (hSigned : Primrec signed) (hModular : Primrec modular)
    (hTag : Primrec testTag) :
    Primrec (fun p => max (reads p) (if testTag p = 3 then modular p else signed p)) :=
  Primrec.nat_max.comp hRead (Primrec.ite (Primrec.eq.comp hTag (Primrec.const 3)) hModular hSigned)

private theorem rowBoundLiteral (p : RawCostArgs) :
    max (rowCode p.2.2.1)
      (if p.2.2.1.1.1 = 3 then weightedTailCode p.1 p.2.2.1.1.2 p.2.2.1.2.2
        else staticCode p.1 p.2.1 (cleanupCode p.2.2.1.2)) =
      rowBound p.1 p.2.1 p.2.2 := rfl

theorem rowBoundPrimitive :
    Primrec (fun p : Nat × Nat × RawBitRow => rowBound p.1 p.2.1 p.2.2) := by
  have cost := maxReadAndCost (rowPrimitive.comp sourceRowPrimitive)
    signedFromBit modularFromBit tagPrimitive
  exact cost.of_eq rowBoundLiteral

private theorem foldBoundPrimitive {X : Type} [Primcodable X] {cost : Nat → Nat → X → Nat}
    (h : Primrec (fun p : Nat × Nat × X => cost p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Nat × Nat × List X => p.2.2.foldr (fun x n => max (cost p.1 p.2.1 x) n) 0) := by
  let A := Nat × Nat × List X
  let S := A × (X × Nat)
  have items : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have b : Primrec (fun p : S => p.1.1) := Primrec.fst.comp Primrec.fst
  have r : Primrec (fun p : S => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have item : Primrec (fun p : S => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : S => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : S => max (cost p.1.1 p.1.2.1 p.2.1) p.2.2) :=
    Primrec.nat_max.comp (h.comp (b.pair (r.pair item))) acc
  exact Primrec.list_foldr items (Primrec.const 0) step.to₂

theorem clauseBoundPrimitive :
    Primrec (fun p : Nat × Nat × List RawBitRow => clauseBound p.1 p.2.1 p.2.2) :=
  (foldBoundPrimitive rowBoundPrimitive).of_eq (fun _ => rfl)

theorem familyBoundPrimitive :
    Primrec (fun p : Nat × Nat × RawFamily => familyBound p.1 p.2.1 p.2.2) :=
  (foldBoundPrimitive clauseBoundPrimitive).of_eq (fun _ => rfl)

theorem exactRawMixedFamilyCeilingEffectivity : ExactRawMixedFamilyCeilingEffectivity :=
  ⟨rowBoundPrimitive,clauseBoundPrimitive,familyBoundPrimitive⟩

end LogicLineages.PermittedControl.ActualRawMixedFamilyCeiling
