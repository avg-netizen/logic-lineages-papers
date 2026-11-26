module
public import LogicLineages.PermittedControl.ActualCanonicalSignFundingTargets
import LogicLineages.PermittedControl.ActualCanonicalSignFundingMassProof
import LogicLineages.PermittedControl.ActualCanonicalZeroAlphabetProof
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualNormalizedTapeOutsideProof
import LogicLineages.PermittedControl.ActualZeroEdgeConstantShiftLedgerProof
import LogicLineages.PermittedControl.ActualSignedReadMassEdgeProof
import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftConstantProof
import LogicLineages.PermittedControl.ActualCountOriginDispositionsLedgerProof
import LogicLineages.PermittedControl.ActualRankedZeroClassSelectionProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalSignFunding
open PreparedProjection ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassCohortTransfer
open ActualRankedZeroClass ActualZeroClassOutsideAndShift ActualShortCountCleanup
open ActualReadChargeIteration ActualZeroEdgeAlphabet ActualSignedReadMass
open ActualZeroEdgeConstantShift ActualCanonicalZeroTrace ActualCanonicalZeroAlphabet
open ActualCanonicalNormalizedTape ActualNormalizedTape

theorem exactCanonicalShift : ExactCanonicalShift := by
  classical
  intro f B ρ r top source out a alphabet edge covered
  obtain ⟨xs,annotations,C,moved,ledger,x₀,q,prepared,moves,_,_,disposed,_,_,_,constantEq,_⟩ := edge
  have tape := exactCanonicalTapeCertificate f ρ source.reads xs prepared.live prepared.grouped
  have normIn (rd : Read) (member : rd ∈ xs) : rd.1.2 ∈ alphabet := by
    obtain ⟨prior,old,key,_⟩ := (tape.records rd member).2.2
    rw [← key]
    exact covered prior old
  let terms := xs.map Prod.fst
  let values := xs.map Prod.snd
  let ps := cohort f C terms annotations
  let anchor := leastPrefix ps
  let outside := outsideCohort f C terms values annotations
  let origins := countOrigins f C xs annotations
  let before := outside ++ moved
  let initialShift := (replaceRow f C terms values annotations).2
  have outsideSub : outside.Sublist xs := by
    change (outsideCohort f C terms values annotations).Sublist xs
    rw [exactTapeOutside f ρ C source.reads xs annotations tape prepared.aligned]
    exact List.filter_sublist
  have originSub : origins.Sublist (classLedger f C xs annotations) := List.filter_sublist
  have originReads : (origins.map Prod.fst).Sublist xs :=
    (originSub.map Prod.fst).trans (exactClassSelection f ρ C xs annotations prepared.aligned).1
  have paidOrigin := (exactCountOrigins f B ρ C xs annotations prepared.aligned prepared.ready).1
  have allOrigins (entry : Origin) (member : entry ∈ origins) :
      OriginPaid f B ρ C entry ∧ entry.1.1.2 ∈ alphabet :=
    ⟨paidOrigin entry member,
      normIn entry.1 (originReads.subset (List.mem_map.mpr ⟨entry,member,rfl⟩))⟩
  have originMass := massSublist originReads
  have installBound : initialShift.natAbs ≤
      signedMass xs * (correctionMaximum alphabet + prefixShortMaximum alphabet) := by
    change (replaceRow f C terms values annotations).2.natAbs ≤ _
    rw [exactOriginShift f ρ C xs annotations anchor ledger moved prepared.aligned disposed]
    exact (ledgerShiftBound f B ρ C anchor origins ledger moved alphabet disposed allOrigins).trans
      (Nat.mul_le_mul_right _ originMass)
  have kept := massSublist outsideSub
  have movedBound := exactOriginMovedMass f ρ anchor origins ledger moved disposed
  have beforeBound : signedMass before ≤ 3 * signedMass xs := by
    change signedMass (outside ++ moved) ≤ _
    rw [massAppend]
    omega
  have beforeCovered : ∀ rd ∈ before, rd.1.2 ∈ expand alphabet :=
    exactCertifiedExpansion f ρ C source.reads xs moved annotations alphabet tape prepared.aligned moves covered
  have cleanBound := (exactCleanupShiftBound before alphabet beforeCovered).trans
    (Nat.mul_le_mul_right (cleanupMaximum alphabet) beforeBound)
  have combineClean : (3 * signedMass xs) * cleanupMaximum alphabet =
      signedMass xs * (3 * cleanupMaximum alphabet) := by
    rw [Nat.mul_comm 3 (signedMass xs),Nat.mul_assoc]
  have delta : out.constant - source.constant = initialShift + shortShift before := by
    change out.constant = source.constant + initialShift + shortShift before at constantEq
    omega
  have normalizedDelta : (out.constant - source.constant).natAbs ≤ signedMass xs * edgeFactor alphabet := by
    rw [delta]
    calc
      _ ≤ initialShift.natAbs + (shortShift before).natAbs := Int.natAbs_add_le _ _
      _ ≤ signedMass xs * (correctionMaximum alphabet + prefixShortMaximum alphabet) +
          (3 * signedMass xs) * cleanupMaximum alphabet := Nat.add_le_add installBound cleanBound
      _ = signedMass xs * edgeFactor alphabet := by
        rw [combineClean,← Nat.mul_add] <;> rfl
  have actualDelta := normalizedDelta.trans
    (Nat.mul_le_mul_right (edgeFactor alphabet) (exactCanonicalNormalizedMass f ρ source.reads xs prepared.live prepared.grouped))
  refine ⟨actualDelta,?_⟩
  calc
    out.constant.natAbs = (source.constant + (out.constant - source.constant)).natAbs :=
      congrArg Int.natAbs (by omega)
    _ ≤ source.constant.natAbs + (out.constant - source.constant).natAbs := Int.natAbs_add_le _ _
    _ ≤ source.constant.natAbs + signedMass source.reads * edgeFactor alphabet :=
      Nat.add_le_add_left actualDelta _

end LogicLineages.PermittedControl.ActualCanonicalSignFunding
