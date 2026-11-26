module
public import LogicLineages.PermittedControl.ActualZeroClassCohortTransferTargets
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferCohortProof
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferMinimumProof
import LogicLineages.PermittedControl.ActualZeroClassCohortTransferPairProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassCohortTransfer
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroClassReplacement

private theorem transferToAnchor (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (ordered : StrictMono ρ) (C : Nat) (anchor : SurvivingPrefix)
    (anchorActual : ActualPrefix f ρ C anchor) (ps : List SurvivingPrefix)
    (actual : ∀ p ∈ ps, ActualPrefix f ρ C p)
    (least : ∀ p ∈ ps, anchor.rank ≤ p.rank)
    (paid : ∀ p ∈ ps, anchor.rank < p.rank →
      pairTail B anchor p ≤ ρ anchor.rank ∧ pairTail B anchor p ≤ ρ p.rank) :
    ∃ out, MovedPrefixes f ρ anchor ps out ∧ liftedReads f ρ out ∧
      readSum (ps.map SurvivingPrefix.asRead) = readSum out ∧
      ∀ read ∈ out, read.1.2.rank = anchor.rank := by
  induction ps with
  | nil => exact ⟨[],.nil,True.intro,rfl,fun read member => False.elim (List.not_mem_nil member)⟩
  | cons p ps next =>
      obtain ⟨out,moved,reads,value,rank⟩ :=
        next (fun q member => actual q (List.mem_cons_of_mem _ member))
          (fun q member => least q (List.mem_cons_of_mem _ member))
          (fun q member => paid q (List.mem_cons_of_mem _ member))
      exact appendMovedPrefix f B selected ρ ordered C anchor p anchorActual
        (actual p List.mem_cons_self) (least p List.mem_cons_self) (paid p List.mem_cons_self)
        ps out moved reads value rank

theorem exactCohortTransfer : ExactCohortTransfer := by
  intro f B selected ρ ordered C terms values annotations aligned
  dsimp only
  intro ready
  let ps := cohort f C terms annotations
  have actual : ∀ p ∈ ps, ActualPrefix f ρ C p :=
    exactCohort.2 f ρ C terms values annotations aligned
  change TransferReady B ρ ps at ready
  change match leastPrefix ps with
    | none => ps = []
    | some anchor =>
        anchor ∈ ps ∧ (∀ p ∈ ps, anchor.rank ≤ p.rank) ∧
        ∃ out, MovedPrefixes f ρ anchor ps out ∧ liftedReads f ρ out ∧
          readSum (ps.map SurvivingPrefix.asRead) = readSum out ∧
          ∀ read ∈ out, read.1.2.rank = anchor.rank
  cases found : leastPrefix ps with
  | none => exact (exactLeastPrefix.1 ps).mp found
  | some anchor =>
      obtain ⟨member,least⟩ := exactLeastPrefix.2 ps anchor found
      exact ⟨member,least,transferToAnchor f B selected ρ ordered C anchor
        (actual anchor member) ps actual least (ready anchor found)⟩

end LogicLineages.PermittedControl.ActualZeroClassCohortTransfer
