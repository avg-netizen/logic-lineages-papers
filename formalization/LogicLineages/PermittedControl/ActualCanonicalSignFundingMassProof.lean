module
public import LogicLineages.PermittedControl.ActualCanonicalSignFundingTargets
import LogicLineages.PermittedControl.ActualSignedReadMassEdgeProof
import LogicLineages.PermittedControl.ActualSignedReadMassNormalizationProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingReadProof
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualNormalizedTapeOutsideProof
import LogicLineages.PermittedControl.ActualRankedZeroClassSelectionProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalSignFunding
open ActualSignedReadMass ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualCanonicalOperandGrouping ActualCanonicalNormalizedTape ActualCanonicalZeroTrace
open ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow ActualRankedZeroClass
open ActualCountOriginDispositions ActualShortCountCleanup ActualNormalizedTape

private theorem massPerm (xs ys : List Read) (p : xs.Perm ys) :
    signedMass xs = signedMass ys := by
  induction p with
  | nil => rfl
  | cons hd tail ih =>
    change hd.1.1.natAbs + signedMass _ = hd.1.1.natAbs + signedMass _
    rw [ih]
  | swap a b tail =>
    change b.1.1.natAbs + (a.1.1.natAbs + signedMass tail) =
      a.1.1.natAbs + (b.1.1.natAbs + signedMass tail)
    exact add_left_comm _ _ _
  | trans p q ihp ihq => exact ihp.trans ihq

theorem exactCanonicalNormalizedMass : ExactCanonicalNormalizedMass := by
  intro f ρ raw xs live canonical
  obtain ⟨old,legacy,_,_,_,_,_⟩ := (exactNormalizedReads f ρ raw).2 live
  obtain ⟨out,ready,perm,_,_,_⟩ := (exactCanonicalReads f ρ raw).2 old legacy
  have same : out = xs := Option.some.inj (ready.symm.trans canonical)
  rw [← same,massPerm out old perm]
  exact exactNormalizedMass f ρ raw old legacy

theorem exactCanonicalEdgeMass : ExactCanonicalEdgeMass := by
  classical
  intro f B ρ r top source out a edge
  obtain ⟨xs,annotations,C,moved,ledger,x₀,q,prepared,_,_,_,disposed,_,_,_,_,literal⟩ := edge
  have tape := exactCanonicalTapeCertificate f ρ source.reads xs prepared.live prepared.grouped
  let outside := outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations
  let origins := countOrigins f C xs annotations
  let anchor := leastPrefix (cohort f C (xs.map Prod.fst) annotations)
  have untouched : outside.Sublist xs := by
    change (outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).Sublist xs
    rw [exactTapeOutside f ρ C source.reads xs annotations tape prepared.aligned]
    exact List.filter_sublist
  have originSub : origins.Sublist (classLedger f C xs annotations) := List.filter_sublist
  have originMass : signedMass (origins.map Prod.fst) ≤ signedMass xs :=
    massSublist ((originSub.map Prod.fst).trans (exactClassSelection f ρ C xs annotations prepared.aligned).1)
  have moves := exactOriginMovedMass f ρ anchor origins ledger moved disposed
  have outsideMass := massSublist untouched
  have beforeMass : signedMass (outside ++ moved) ≤ 3 * signedMass xs := by
    rw [massAppend]
    omega
  have cleaned : (retained (outside ++ moved)).Sublist (outside ++ moved) := List.filter_sublist
  change out.reads = retained (outside ++ moved) at literal
  rw [literal]
  exact (massSublist cleaned).trans
    (beforeMass.trans (Nat.mul_le_mul_left 3 (exactCanonicalNormalizedMass f ρ source.reads xs prepared.live prepared.grouped)))

end LogicLineages.PermittedControl.ActualCanonicalSignFunding
