module
public import LogicLineages.PermittedControl.ActualRawSignedCleanupTargets
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawSignedCleanup
open FieldComparison
open PreparedProjection (LowerOperandCode)
open MixedSameRankResidue (WeightedCode)
open ActualRawSignedStaticCeiling (RawSyntax)
open ActualEffectiveTerminalSignBound (shortLengthCode)
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof

theorem shortPrimitive : Primrec shortLengthCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have endpoints : Primrec (fun op : LowerOperandCode => op.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have slot : Primrec (fun op : LowerOperandCode => shortGapLengthCode op.2.2.2.2.1 op.2.2.2.2.2) :=
    shortFieldPreprocessingEffective.2.1.comp (Primrec.fst.comp endpoints) (Primrec.snd.comp endpoints)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) slot (Primrec.const 0)

private theorem lenPrimitive : Primrec (fun t : WeightedCode => shortLengthCode t.2) :=
  shortPrimitive.comp Primrec.snd

theorem retainPrimitive : Primrec retainCode :=
  Primrec.listFilter (Primrec.eq.comp lenPrimitive (Primrec.const 0))

private theorem correctionPrimitive : Primrec (fun t : WeightedCode => t.1 * (shortLengthCode t.2 : Int)) :=
  mul_primitive.comp Primrec.fst (ofNat_primitive.comp lenPrimitive)

theorem shiftPrimitive : Primrec shiftCode := by
  let A := List WeightedCode × (WeightedCode × Int)
  have term : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const (0 : Int))
    (add_primitive.comp (correctionPrimitive.comp term) acc).to₂

theorem cleanupPrimitive : Primrec cleanupCode := by
  have terms : Primrec (Prod.snd : RawSyntax → List WeightedCode) := Primrec.snd
  exact (add_primitive.comp Primrec.fst (shiftPrimitive.comp terms)).pair (retainPrimitive.comp terms)

theorem exactRawInitialCleanupEffectivity : ExactRawInitialCleanupEffectivity :=
  ⟨shortPrimitive,retainPrimitive,shiftPrimitive,cleanupPrimitive⟩

end LogicLineages.PermittedControl.ActualRawSignedCleanup
