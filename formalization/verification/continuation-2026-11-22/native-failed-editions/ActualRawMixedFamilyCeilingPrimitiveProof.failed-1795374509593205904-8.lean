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

theorem rowBoundPrimitive :
    Primrec (fun p : Nat × Nat × RawBitRow => rowBound p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × RawBitRow
  have b : Primrec (fun p : A => p.1) := Primrec.fst
  have r : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have row : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have header : Primrec (fun p : A => p.2.2.1.1) := Primrec.fst.comp row
  have tag : Primrec (fun p : A => p.2.2.1.1.1) := Primrec.fst.comp header
  have modulus : Primrec (fun p : A => p.2.2.1.1.2) := Primrec.snd.comp header
  have syntax : Primrec (fun p : A => p.2.2.1.2) := Primrec.snd.comp row
  have terms : Primrec (fun p : A => p.2.2.1.2.2) := Primrec.snd.comp syntax
  have modularBound : Primrec (fun p : A => weightedTailCode p.1 p.2.2.1.1.2 p.2.2.1.2.2) :=
    MixedSameRankResidue.codeExact.2.1.comp (b.pair (modulus.pair terms))
  have signedBound : Primrec (fun p : A => staticCode p.1 p.2.1 (cleanupCode p.2.2.1.2)) :=
    staticPrimitive.comp (b.pair (r.pair (cleanupPrimitive.comp syntax)))
  have branch := Primrec.ite (Primrec.eq.comp tag (Primrec.const 3)) modularBound signedBound
  exact (Primrec.nat_max.comp (rowPrimitive.comp row) branch).of_eq (fun _ => rfl)

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
