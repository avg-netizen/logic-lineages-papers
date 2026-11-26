module
public import LogicLineages.PermittedControl.ActualZeroClassReplacementTargets
import LogicLineages.PermittedControl.SelectedCountOnlyClassProof
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.EntryLinearProof
import LogicLineages.PermittedControl.EntryResiduesProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassReplacement
open OrdinalComparison FieldComparison PreparedProjection
open SelectedCountOnlyClass (prefixTarget prefixNotationExact)

theorem exactPrefixRead : ExactPrefixRead := by
  intro f ρ rank lam mu v i actual
  dsimp only
  intro below first
  let eta := prefixTarget mu
  let x := ρ rank
  change eta.1.repr ≤ lam.1.repr at below
  change FirstEntry f (countInitial lam.1.repr x) eta.1.repr i at first
  have lamLimit : Order.IsSuccLimit lam.1.repr := actual.1.1.1
  have lamAffordable : actualOrdinalNorm lam.1.repr ≤ x := actual.1.2
  have lamBound := normalRepresentationSound lam
  have etaLimit : Order.IsSuccLimit eta.1.repr := by
    rw [show eta.1.repr = mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0})
      from prefixNotationExact.2 mu]
    exact Ordinal.isSuccLimit_add _ square_facts.2.2
  have identity : i = 0 ↔ eta.1.repr = lam.1.repr := by
    constructor
    · intro zero
      rcases below.eq_or_lt with equal | strict
      · exact equal
      · have positive := proper_entry_pos f lam.1.repr eta.1.repr x i lamLimit strict first
        omega
    · intro equal
      have zero := (identityEntry f lam.1.repr x lamBound (.inr lamLimit) lamAffordable).1
      have paid : FirstEntry f (countInitial lam.1.repr x) lam.1.repr i := by
        rw [← equal]
        exact first
      exact firstEntry_unique f _ _ i 0 paid zero
  refine ⟨identity,?_⟩
  intro nonzero
  have strict : eta.1.repr < lam.1.repr :=
    lt_of_le_of_ne below (fun equal => nonzero (identity.mpr equal))
  have domain : ClosedOrdinaryValueDomain (.entry 0 lam eta) x :=
    ⟨⟨lamLimit,.inr etaLimit,strict⟩,lamAffordable⟩
  have read := (((closedOrdinaryCountActual f lam eta x).2 domain).1 i).mpr first
  exact ⟨⟨domain,first⟩,read⟩

theorem exactShortPrefix (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (rank : Nat) (lam eta : NONote) (i : Nat)
    (proper : LowerOperandActual f ρ (.count rank lam eta) i)
    (short : 0 < shortGapLength lam eta)
    (tail : max (actualOrdinalNorm lam.1.repr)
      (max (actualOrdinalNorm eta.1.repr + 3) (max 1 B)) ≤ ρ rank) :
    i = shortGapLength lam eta := by
  obtain ⟨⟨lamLimit,etaLimit,below⟩,_⟩ := proper.1
  obtain ⟨j,first,_,shortCount,_⟩ :=
    entryResidues f B selected 1 lam.1.repr eta.1.repr (ρ rank) (by decide)
      (normalRepresentationSound lam) lamLimit etaLimit below tail
  have shape := (shortGapRecognition lam eta proper.1.1 (shortGapLength lam eta) short).2.2.mp rfl
  exact (firstEntry_unique f _ _ i j proper.2 first).trans
    (shortCount (shortGapLength lam eta) short shape)

end LogicLineages.PermittedControl.ActualZeroClassReplacement
