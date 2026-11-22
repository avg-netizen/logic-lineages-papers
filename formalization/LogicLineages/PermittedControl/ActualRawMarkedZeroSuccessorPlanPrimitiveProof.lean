module
public import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorTargets
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.OrdinalComparison.RawComparisonProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.PermittedControl.OrdinalEndpointProgramsProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison
open ActualCountCoreLabels (rawTag)
open SelectedCountOnlyClass (omegaSquareNote)

private theorem etaPrimitive : Primrec etaCode :=
  ordinalAddCodeEffective.comp Primrec.id (Primrec.const (rawNoteEncode omegaSquareNote.1))

private theorem corePrimitive : Primrec coreCode := by
  have norm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have half := Primrec.nat_div.comp (Primrec.succ.comp norm) (Primrec.const 2)
  have cast := IntegerAlgorithms.Proof.ofNat_primitive.comp half
  exact (IntegerAlgorithms.Proof.add_primitive.comp (Primrec.const (1 : Int))
    (IntegerAlgorithms.Proof.negate_primitive.comp cast)).of_eq
    (fun _ => by unfold coreCode; rw [sub_eq_add_neg] <;> rfl)

private theorem tagPrimitive : Primrec (fun p : Nat × Nat => rawTag p.1 p.2) := by
  let A := Nat × Nat
  have lam : Primrec (Prod.fst : A → Nat) := Primrec.fst
  have mu : Primrec (Prod.snd : A → Nat) := Primrec.snd
  have norm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have guard := closedProperEntryDomainExact.1.comp (lam.pair (mu.pair (norm.comp lam)))
  have short := shortFieldPreprocessingEffective.2.1.comp lam mu
  have eta := ordinalAddCodeEffective.comp mu (Primrec.const (rawNoteEncode omegaSquareNote.1))
  have cmp := rawComparisonPrimitiveRecursive.comp eta lam
  have shape : Primrec (fun p : A =>
      if rawComparisonCode (ordinalAddCode p.2 (rawNoteEncode omegaSquareNote.1)) p.1 = 1 then 2
      else if rawComparisonCode (ordinalAddCode p.2 (rawNoteEncode omegaSquareNote.1)) p.1 = 0 then 3 else 0) :=
    Primrec.ite (Primrec.eq.comp cmp (Primrec.const 1)) (Primrec.const 2)
      (Primrec.ite (Primrec.eq.comp cmp (Primrec.const 0)) (Primrec.const 3) (Primrec.const 0))
  have middle := Primrec.ite (Primrec.eq.comp short (Primrec.const 0)) shape (Primrec.const 1)
  apply (Primrec.cond guard middle (Primrec.const 0)).of_eq
  rintro ⟨lam,mu⟩
  unfold rawTag
  dsimp only
  cases h : closedProperEntryGuard (lam,mu,rawNormCode lam) <;> rfl

private theorem planPrimitive : Primrec planCode := by
  let A := Nat × Nat
  have eta : Primrec (fun p : A => etaCode p.2) := etaPrimitive.comp Primrec.snd
  have short : Primrec (fun p : A => shortGapLengthCode p.1 (etaCode p.2)) :=
    shortFieldPreprocessingEffective.2.1.comp Primrec.fst eta
  have proper : Primrec (fun p : A => some (1,etaCode p.2,shortGapLengthCode p.1 (etaCode p.2))) :=
    Primrec.option_some.comp ((Primrec.const 1).pair (eta.pair short))
  exact Primrec.ite (Primrec.eq.comp tagPrimitive (Primrec.const 2))
    (Primrec.const (some ((0,0,0) : PlanCode)))
    (Primrec.ite (Primrec.eq.comp tagPrimitive (Primrec.const 3)) proper (Primrec.const none))

private theorem opPrimitive : Primrec (fun m : MarkCode => m.1.2) :=
  Primrec.snd.comp Primrec.fst

private theorem endsPrimitive : Primrec endpoints :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem selectedPrimitive : PrimrecPred (fun m : MarkCode => m.2 = true) :=
  Primrec.eq.comp Primrec.snd (Primrec.const true)

theorem shiftOnePrimitive : Primrec shiftOneCode := by
  let A := MarkCode × PlanCode
  have w : Primrec (fun p : A => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have tag : Primrec (fun m : MarkCode => m.1.2.1) := Primrec.fst.comp opPrimitive
  have ends := endsPrimitive.comp opPrimitive
  have muCode : Primrec (fun p : A => (endpoints p.1.1.2).2) :=
    Primrec.snd.comp (ends.comp Primrec.fst)
  have len : Primrec (fun p : A => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have actual : Primrec (fun p : A =>
      p.1.1.1 * (coreCode (endpoints p.1.1.2).2 + (p.2.2.2 : Int))) :=
    IntegerAlgorithms.Proof.mul_primitive.comp w
      (IntegerAlgorithms.Proof.add_primitive.comp (corePrimitive.comp muCode)
        (IntegerAlgorithms.Proof.ofNat_primitive.comp len))
  have counting := Primrec.option_map (planPrimitive.comp ends) actual.to₂
  exact Primrec.ite selectedPrimitive
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) counting
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) (Primrec.const (some (0 : Int))) (Primrec.const none)))
    (Primrec.const (some 0))

theorem markedPrefixPrimitive : Primrec markedPrefixCode := by
  let A := MarkCode × PlanCode
  have tag : Primrec (fun m : MarkCode => m.1.2.1) := Primrec.fst.comp opPrimitive
  have ends := endsPrimitive.comp opPrimitive
  have rank : Primrec (fun p : A => p.1.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (opPrimitive.comp Primrec.fst))
  have lam : Primrec (fun p : A => (endpoints p.1.1.2).1) :=
    Primrec.fst.comp (ends.comp Primrec.fst)
  have w : Primrec (fun p : A => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have mode : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have eta : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have len : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have prefixBranch : Primrec (fun p : A =>
      if p.2.1 = 1 ∧ p.2.2.2 = 0 then
        some (p.1.1.2.2.1,(endpoints p.1.1.2).1,p.2.2.1,p.1.1.1) else none) :=
    Primrec.ite ((Primrec.eq.comp mode (Primrec.const 1)).and (Primrec.eq.comp len (Primrec.const 0)))
      (Primrec.option_some.comp (rank.pair (lam.pair (eta.pair w)))) (Primrec.const none)
  have result := Primrec.option_bind (planPrimitive.comp ends) prefixBranch.to₂
  exact Primrec.ite selectedPrimitive (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) result
    (Primrec.const none)) (Primrec.const none)

end LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessor
