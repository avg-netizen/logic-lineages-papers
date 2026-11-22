module
public import LogicLineages.PermittedControl.ActualZeroEdgeConstantShiftTargets
public import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroEdgeConstantShift
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualCountOriginDispositions ActualZeroClassCohortTransfer ActualZeroClassOutsideAndShift
open ActualZeroClassCommonTail ActualZeroEdgeAlphabet ActualSignedReadMass ActualShortCountCleanup
open SelectedCountOnlyClass (prefixTarget)
open InnerTerminationTargets (Disposition)

private theorem finiteMaxMember {α : Type} (cost : α → Nat) (items : List α) (a : α)
    (member : a ∈ items) : cost a ≤ finiteMax cost items := by
  induction items with
  | nil => cases member
  | cons head items ih =>
      change cost a ≤ max (cost head) (finiteMax cost items)
      rcases List.mem_cons.mp member with eq | later
      · subst a
        exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

theorem exactDispositionShiftBound : ExactDispositionShiftBound := by
  intro f B ρ C anchor entry d out alphabet paid outcome member
  obtain ⟨rd,ann⟩ := entry
  have isCount := paid.2.2.2.2.2
  cases ann with
  | zeroWeight => cases isCount
  | linear => cases isCount
  | ordinary q => cases isCount
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,key,_,_,_,_,_,κExact,_,_⟩ := paid.2.2.1
      have keyMember : LowerOperand.count rank lam mu ∈ alphabet := by
        rw [← key]
        exact member
      have corr : κ.natAbs ≤ correctionMaximum alphabet := by
        rw [κExact]
        exact finiteMaxMember correctionBound alphabet (.count rank lam mu) keyMember
      have prefixMember : (⟨rank,lam,prefixTarget mu⟩ : PrefixLabel) ∈ prefixCandidates alphabet :=
        List.mem_filterMap.mpr ⟨.count rank lam mu,keyMember,rfl⟩
      have short : shortGapLength lam (prefixTarget mu) ≤ prefixShortMaximum alphabet :=
        finiteMaxMember (fun label : PrefixLabel => shortGapLength label.lam label.eta)
          (prefixCandidates alphabet) ⟨rank,lam,prefixTarget mu⟩ prefixMember
      have corrAnd : κ.natAbs ≤ correctionMaximum alphabet + prefixShortMaximum alphabet :=
        corr.trans (Nat.le_add_right _ _)
      have literal : rd = ((rd.1.1,LowerOperand.count rank lam mu),rd.2) :=
        Prod.ext (Prod.ext rfl key) rfl
      have literalOutcome : OriginOutcome f ρ anchor
          (((rd.1.1,LowerOperand.count rank lam mu),rd.2),.count i q κ) d out := by
        rw [← literal]
        exact outcome
      simp only [OriginOutcome] at literalOutcome
      have head := literalOutcome.2
      by_cases identity : i = 0
      · simp only [if_pos identity] at head
        obtain ⟨_,kind,_⟩ := head
        simpa only [kind,Disposition.shift] using corrAnd
      · by_cases long : shortGapLength lam (prefixTarget mu) = 0
        · simp only [if_neg identity,if_pos long] at head
          obtain ⟨pivot,_,_,_,tail⟩ := head
          by_cases same : rank = pivot.rank
          · simp only [if_pos same] at tail
            obtain ⟨_,kind,_⟩ := tail
            simpa only [kind,Disposition.shift] using corrAnd
          · simp only [if_neg same] at tail
            obtain ⟨_,h,_,_,kind,_⟩ := tail
            simpa only [kind,Disposition.shift] using corrAnd
        · simp only [if_neg identity,if_neg long] at head
          obtain ⟨_,kind,_⟩ := head
          rw [kind,Disposition.shift]
          exact (Int.natAbs_add_le _ _).trans
            (Nat.add_le_add corr (by simpa only [Int.natAbs_natCast] using short))

theorem ledgerShiftBound (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat)
    (anchor : Option SurvivingPrefix) (origins : List Origin)
    (ledger : List (Origin × CountDisposition)) (out : List Read) (alphabet : List LowerOperand)
    (steps : DisposedOrigins f ρ anchor origins ledger out) :
    (∀ entry ∈ origins, OriginPaid f B ρ C entry ∧ entry.1.1.2 ∈ alphabet) →
    (weightedOriginShift ledger).natAbs ≤
      signedMass (origins.map Prod.fst) * (correctionMaximum alphabet + prefixShortMaximum alphabet) := by
  induction steps with
  | nil => intro _; exact Nat.zero_le _
  | @cons entry origins d ledger first rest outcome _ ih =>
      intro sources
      obtain ⟨paid,member⟩ := sources entry List.mem_cons_self
      have factor := exactDispositionShiftBound f B ρ C anchor entry d first alphabet paid outcome member
      have tail := ih (fun a ha => sources a (List.mem_cons_of_mem _ ha))
      let K := correctionMaximum alphabet + prefixShortMaximum alphabet
      change (entry.1.1.1 * d.shift + weightedOriginShift ledger).natAbs ≤
        (entry.1.1.1.natAbs + signedMass (origins.map Prod.fst)) * K
      rw [Nat.add_mul]
      apply (Int.natAbs_add_le _ _).trans
      apply Nat.add_le_add _ tail
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ factor

theorem exactCleanupShiftBound : ExactCleanupShiftBound := by
  intro before alphabet
  induction before with
  | nil => intro _; exact Nat.zero_le _
  | cons rd before ih =>
      intro coverage
      have cost : shortLength rd.1.2 ≤ cleanupMaximum alphabet :=
        finiteMaxMember shortLength (expand alphabet) rd.1.2 (coverage rd List.mem_cons_self)
      have tail := ih (fun a ha => coverage a (List.mem_cons_of_mem _ ha))
      change (rd.1.1 * (shortLength rd.1.2 : Int) + shortShift before).natAbs ≤
        (rd.1.1.natAbs + signedMass before) * cleanupMaximum alphabet
      rw [Nat.add_mul]
      apply (Int.natAbs_add_le _ _).trans
      apply Nat.add_le_add _ tail
      rw [Int.natAbs_mul,Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ cost

end LogicLineages.PermittedControl.ActualZeroEdgeConstantShift
