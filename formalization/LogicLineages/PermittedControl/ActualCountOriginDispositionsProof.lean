module
public import LogicLineages.PermittedControl.ActualCountOriginDispositionsTargets
import LogicLineages.PermittedControl.ActualCountOriginDispositionsLedgerProof
import LogicLineages.PermittedControl.ActualCountOriginDispositionsHeadProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountOriginDispositions
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroClassReplacement ActualZeroClassCohortTransfer

private theorem disposeOrigins (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (C : Nat) (anchor : Option SurvivingPrefix)
    (entries : List Origin) (out : List Read)
    (origin : ∀ entry ∈ entries, OriginPaid f B ρ C entry)
    (moved : MovedAt f ρ anchor (originSurvivors f C entries) out)
    (reads : liftedReads f ρ out) :
    ∃ ledger, DisposedOrigins f ρ anchor entries ledger out := by
  induction entries generalizing out with
  | nil =>
      cases anchor with
      | none =>
          have empty : out = [] := moved.2
          subst out
          exact ⟨[],.nil⟩
      | some anchor =>
          change MovedPrefixes f ρ anchor [] out at moved
          cases moved
          exact ⟨[],.nil⟩
  | cons entry entries next =>
      rw [originSurvivorsCons] at moved
      obtain ⟨d,first,tail,whole,head,tailMoved,tailReads⟩ :=
        headDisposition f B selected ρ C entry anchor (originSurvivors f C entries) out
          (origin entry List.mem_cons_self) moved reads
      obtain ⟨ledger,rest⟩ := next tail
        (fun current member => origin current (List.mem_cons_of_mem _ member)) tailMoved tailReads
      subst out
      exact ⟨(entry,d)::ledger,.cons head rest⟩

theorem exactOriginDispositions : ExactOriginDispositions := by
  intro f B selected ρ C xs annotations aligned ready
  dsimp only
  intro anchor out _ moved reads
  obtain ⟨paid,projection⟩ := exactCountOrigins f B ρ C xs annotations aligned ready
  refine disposeOrigins f B selected ρ C anchor (countOrigins f C xs annotations) out paid ?_ reads
  rw [projection]
  exact moved

end LogicLineages.PermittedControl.ActualCountOriginDispositions
