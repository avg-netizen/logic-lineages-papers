module
public import LogicLineages.PermittedControl.ActualCanonicalSignFundingTargets
import LogicLineages.PermittedControl.ActualCanonicalSignFundingMassProof
import LogicLineages.PermittedControl.ActualCanonicalSignFundingTraceProof
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTraceProof
import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundDominanceProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalSignFunding
open PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualFiniteGlobalTail ActualZeroEdgeAlphabet ActualTraceSignCutoff
open ActualZeroClassCommonTail ActualSignedReadMass ActualZeroEdgeConstantShift
open ActualCanonicalNormalizedTape ActualCanonicalReachedFunding ActualEffectiveTerminalSignBound

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

theorem exactCanonicalSignFunding : ExactCanonicalSignFunding := by
  classical
  intro f B selected ρ r top initial reached answers initialLive initialRank initialLong path xs normalized
  let alphabet := globalAlphabet r (syntaxOf initial)
  let terms := xs.map Prod.fst
  obtain ⟨live,_,_,_,covered⟩ := exactCanonicalReachFacts f B selected ρ r top
    initial reached answers initialLive initialRank initialLong path
  have tape := exactCanonicalTapeCertificate f ρ reached.reads xs live normalized
  have keys (rd : Read) (member : rd ∈ xs) : rd.1.2 ∈ alphabet := by
    obtain ⟨prior,old,op,_⟩ := (tape.records rd member).2.2
    rw [← op]
    exact covered prior old
  have mass := (exactCanonicalNormalizedMass f ρ reached.reads xs live normalized).trans
    (exactCanonicalTraceMass f B selected ρ r top initial reached answers path).2
  have constant := (exactCanonicalTraceConstant f B selected ρ r top initial reached answers
    initialLive initialRank initialLong path).2
  have slopeBoundHere : slopeBound terms ≤ 2 * massCeiling r initial :=
    (slopeMass xs).le.trans (Nat.mul_le_mul_left 2 mass)
  have offsetBoundHere : offsetBound terms ≤ massCeiling r initial * correctionMaximum alphabet :=
    (offsetMass xs alphabet keys).trans (Nat.mul_le_mul_right _ mass)
  have numeric : SelectedLeadingSignCutoff.cutoff (slopeBound terms)
      (reached.constant.natAbs + offsetBound terms) ≤ terminalCutoffCeiling r initial := by
    unfold terminalCutoffCeiling SelectedLeadingSignCutoff.cutoff
    exact Nat.mul_le_mul_left 4
      (Nat.add_le_add_right (Nat.add_le_add slopeBoundHere (Nat.add_le_add constant offsetBoundHere)) 2)
  have localBound : rowCutoffCode reached.constant (terms.map encodeWeighted) ≤ terminalCutoffCeiling r initial := by
    rw [exactEffectiveCutoff.2 reached.constant terms]
    exact numeric
  have rawBound := localBound.trans (exactSignBoundDominance r initial)
  exact ⟨localBound,rawBound,fun paid => rawBound.trans paid⟩

end LogicLineages.PermittedControl.ActualCanonicalSignFunding
