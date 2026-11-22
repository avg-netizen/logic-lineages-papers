module
public import LogicLineages.PermittedControl.ActualSignedReadMassTargets
import LogicLineages.PermittedControl.ActualSignedReadMassNormalizationProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftComplementProof
import LogicLineages.PermittedControl.ActualRankedZeroClassSelectionProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedReadMass
open FieldComparison PreparedProjection ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualCountOriginDispositions ActualZeroClassCohortTransfer ActualReadChargeIteration
open ActualRankedZeroClass ActualZeroClassOutsideAndShift ActualZeroClassRecombinedRow
open ActualShortCountCleanup
open SelectedCountOnlyClass (prefixTarget)

theorem massAppend (left right : List Read) :
    signedMass (left ++ right) = signedMass left + signedMass right := by
  simp only [signedMass,List.map_append,List.sum_append]

theorem massSublist {left right : List Read} (sub : left.Sublist right) :
    signedMass left ≤ signedMass right := by
  induction sub with
  | slnil => exact le_rfl
  | cons rd _ ih =>
      simp only [signedMass,List.map_cons,List.sum_cons] at *
      omega
  | cons_cons rd _ ih =>
      simp only [signedMass,List.map_cons,List.sum_cons] at *
      exact Nat.add_le_add_left ih _

private theorem headMass (f ρ : Nat → Nat) (anchor : Option SurvivingPrefix)
    (entry : Origin) (disposition : CountDisposition) (out : List Read)
    (outcome : OriginOutcome f ρ anchor entry disposition out) :
    signedMass out ≤ 2 * entry.1.1.1.natAbs := by
  obtain ⟨⟨⟨a,op⟩,v⟩,ann⟩ := entry
  cases op <;> cases ann <;> simp only [OriginOutcome] at outcome
  all_goals try exact outcome.2.elim
  rename_i rank lam mu i E κ
  have head := outcome.2
  by_cases identity : i = 0
  · simp only [if_pos identity] at head
    obtain ⟨_,_,rfl⟩ := head
    exact Nat.zero_le _
  · by_cases long : shortGapLength lam (prefixTarget mu) = 0
    · simp only [if_neg identity,if_pos long] at head
      obtain ⟨pivot,_,_,_,tail⟩ := head
      by_cases equalRank : rank = pivot.rank
      · simp only [if_pos equalRank] at tail
        obtain ⟨_,_,rfl⟩ := tail
        change a.natAbs + 0 ≤ 2 * a.natAbs
        omega
      · simp only [if_neg equalRank] at tail
        obtain ⟨_,j,_,_,_,rfl⟩ := tail
        change a.natAbs + ((-a).natAbs + 0) ≤ 2 * a.natAbs
        rw [Int.natAbs_neg]
        omega
    · simp only [if_neg identity,if_neg long] at head
      obtain ⟨_,_,rfl⟩ := head
      exact Nat.zero_le _

theorem exactOriginMovedMass : ExactOriginMovedMass := by
  intro f ρ anchor origins ledger out done
  induction done with
  | nil => exact Nat.zero_le _
  | @cons a entries disposition tail first rest outcome _ ih =>
      rw [massAppend]
      change signedMass first + signedMass rest ≤
        2 * (a.1.1.1.natAbs + signedMass (entries.map Prod.fst))
      have head := headMass f ρ anchor a disposition first outcome
      omega

theorem exactZeroEdgeMass : ExactZeroEdgeMass := by
  classical
  intro f B ρ r zRank source out edge
  obtain ⟨xs,annotations,C,moved,ledger,x₀,q,norm,_,_,chosen,_,_,_,_,_,_,disposed,_,_,_,_,literal⟩ :=
    edge.actual
  have paid : liftedReads f ρ source.reads := by
    by_contra unpaid
    have failure := (exactNormalizedReads f ρ source.reads).1.mpr unpaid
    rw [norm] at failure
    cases failure
  let outside := outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations
  let origins := countOrigins f C xs annotations
  let anchor := leastPrefix (cohort f C (xs.map Prod.fst) annotations)
  have untouched : outside.Sublist xs := by
    change (outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).Sublist xs
    rw [exactOutsideClass f ρ C source.reads xs annotations paid norm chosen.1]
    exact List.filter_sublist
  have originSub : origins.Sublist (classLedger f C xs annotations) := List.filter_sublist
  have originMass : signedMass (origins.map Prod.fst) ≤ signedMass xs :=
    massSublist ((originSub.map Prod.fst).trans (exactClassSelection f ρ C xs annotations chosen.1).1)
  have moves := exactOriginMovedMass f ρ anchor origins ledger moved disposed
  have outsideMass := massSublist untouched
  have beforeMass : signedMass (outside ++ moved) ≤ 3 * signedMass xs := by
    rw [massAppend]
    omega
  have cleaned : (retained (outside ++ moved)).Sublist (outside ++ moved) := List.filter_sublist
  change out.reads = retained (outside ++ moved) at literal
  rw [literal]
  exact (massSublist cleaned).trans
    (beforeMass.trans (Nat.mul_le_mul_left 3 (exactNormalizedMass f ρ source.reads xs norm)))

theorem exactTraceMass : ExactTraceMass := by
  intro f B ρ r zRank n source out path
  induction path with
  | nil s => simp
  | @cons n s t u edge suffix ih =>
      calc
        signedMass u.reads ≤ 3 ^ n * signedMass t.reads := ih
        _ ≤ 3 ^ n * (3 * signedMass s.reads) :=
          Nat.mul_le_mul_left _ (exactZeroEdgeMass f B ρ r zRank s t edge)
        _ = 3 ^ (n+1) * signedMass s.reads := by rw [Nat.pow_succ,Nat.mul_assoc]

end LogicLineages.PermittedControl.ActualSignedReadMass
