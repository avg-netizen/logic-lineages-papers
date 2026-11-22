module
public import LogicLineages.PermittedControl.ActualTraceSignCutoffTargets
import LogicLineages.PermittedControl.ActualTraceSignCutoffConstantProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailEnclosureProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualSignedReadMassNormalizationProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualTraceSignCutoff
open PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingSum ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualReadChargeIteration ActualFiniteGlobalTail ActualZeroEdgeAlphabet
open ActualZeroClassCommonTail ActualSignedReadMass ActualZeroEdgeConstantShift

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

private theorem slopeMass (reads : List Read) :
    slopeBound (reads.map Prod.fst) = 2 * signedMass reads := by
  induction reads with
  | nil => rfl
  | cons rd reads ih =>
      change 2 * rd.1.1.natAbs + slopeBound (reads.map Prod.fst) =
        2 * (rd.1.1.natAbs + signedMass reads)
      rw [ih,Nat.mul_add]

private theorem offsetMass (reads : List Read) (alphabet : List LowerOperand) :
    (∀ rd ∈ reads, rd.1.2 ∈ alphabet) →
    offsetBound (reads.map Prod.fst) ≤ signedMass reads * correctionMaximum alphabet := by
  induction reads with
  | nil => intro _; exact Nat.zero_le _
  | cons rd reads ih =>
      intro covered
      have weight := finiteMaxMember correctionBound alphabet rd.1.2 (covered rd List.mem_cons_self)
      have tail := ih (fun a ha => covered a (List.mem_cons_of_mem _ ha))
      change rd.1.1.natAbs * correctionBound rd.1.2 + offsetBound (reads.map Prod.fst) ≤
        (rd.1.1.natAbs + signedMass reads) * correctionMaximum alphabet
      rw [Nat.add_mul]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ weight) tail

theorem exactReachedCutoffDominance : ExactReachedCutoffDominance := by
  classical
  intro f B ρ r zRank n initial reached path xs normalized
  let alphabet := globalAlphabet r (syntaxOf initial)
  let terms := xs.map Prod.fst
  have live : liftedReads f ρ reached.reads := by
    by_contra unpaid
    have failure := (exactNormalizedReads f ρ reached.reads).1.mpr unpaid
    rw [normalized] at failure
    cases failure
  obtain ⟨out,success,_,_,_,_,records⟩ := (exactNormalizedReads f ρ reached.reads).2 live
  have same : out = xs := Option.some.inj (success.symm.trans normalized)
  subst out
  have covered := exactGlobalLabelEnclosure f B ρ r zRank n initial reached path
  have keys (rd : Read) (member : rd ∈ xs) : rd.1.2 ∈ alphabet := by
    obtain ⟨prior,old,op,_⟩ := (records rd member).2.2
    rw [← op]
    exact covered prior old
  have mass := (exactNormalizedMass f ρ reached.reads xs normalized).trans
    (exactReachMassCeiling f B ρ r zRank n initial reached path)
  have constant := (exactTraceConstantCeiling f B ρ r zRank n initial reached path).2
  have slopeBoundHere : slopeBound terms ≤ 2 * massCeiling r initial :=
    (slopeMass xs).le.trans (Nat.mul_le_mul_left 2 mass)
  have offsetBoundHere : offsetBound terms ≤ massCeiling r initial * correctionMaximum alphabet :=
    (offsetMass xs alphabet keys).trans (Nat.mul_le_mul_right _ mass)
  have numeric : SelectedLeadingSignCutoff.cutoff (slopeBound terms)
      (reached.constant.natAbs + offsetBound terms) ≤ terminalCutoffCeiling r initial := by
    unfold terminalCutoffCeiling SelectedLeadingSignCutoff.cutoff
    exact Nat.mul_le_mul_left 4
      (Nat.add_le_add_right (Nat.add_le_add slopeBoundHere (Nat.add_le_add constant offsetBoundHere)) 2)
  refine ⟨numeric,?_⟩
  rw [exactEffectiveCutoff.2 reached.constant terms]
  exact numeric

theorem fullActualTraceSignCutoff : FullActualTraceSignCutoff :=
  ⟨exactReachMassCeiling,exactTraceConstantCeiling,exactReachedCutoffDominance⟩

end LogicLineages.PermittedControl.ActualTraceSignCutoff
