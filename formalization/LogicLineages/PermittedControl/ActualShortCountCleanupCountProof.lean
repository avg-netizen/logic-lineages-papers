module
public import LogicLineages.PermittedControl.ActualShortCountCleanupTargets
import LogicLineages.PermittedControl.EntryLinearProof
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.ActualShortCountCleanup
open OrdinalComparison FieldComparison PreparedProjection

theorem exactPositiveShortCount : ExactPositiveShortCount := by
  intro f B selected ρ rank lam mu v short actual
  let k := shortGapLength lam mu
  let n := ρ rank - actualOrdinalNorm lam.1.repr
  have proper : ProperField (.entry 0 lam mu) := actual.1.1
  have endpoints : lam.1.repr = mu.1.repr + Ordinal.omega0 * (k : Ordinal) :=
    (shortGapRecognition lam mu k short).2.2.mp rfl
  have muEps := proper.2.2.trans (normalRepresentationSound lam)
  have first := linear_entry f (selected_threshold_admissible f B selected).2
    mu.1.repr proper.2.1 muEps k n
  have start : countInitial lam.1.repr (ρ rank) =
      mu.1.repr + (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) := by
    change lam.1.repr + (n : Ordinal) = _
    rw [endpoints,add_assoc]
  rw [← start] at first
  exact firstEntry_unique f _ _ v k actual.2 first

theorem exactIdentityBoundary : ExactIdentityBoundary := by
  constructor
  · intro f ρ rank lam mu v actual
    exact proper_entry_pos f lam.1.repr mu.1.repr (ρ rank) v
      actual.1.1.1 actual.1.1.2.2 actual.2
  · intro f ρ rank lam mu equal
    have impossible : ¬ ClosedOrdinaryValueDomain (.entry 0 lam mu) (ρ rank) := by
      intro domain
      exact (ne_of_lt domain.1.2.2) equal.symm
    refine ⟨(closedOrdinaryCountActual f lam mu (ρ rank)).1.mpr impossible, ?_⟩
    intro v actual
    exact impossible actual.1

theorem longOfRetained (f ρ : Nat → Nat) (op : LowerOperand) (v : Nat)
    (actual : LowerOperandActual f ρ op v) (notShort : shortLength op = 0) :
    LongCountOperand op := by
  cases op with
  | coordinate rank => trivial
  | ordinary rank field => trivial
  | count rank lam mu =>
      have hp : ProperField (.entry 0 lam mu) := actual.1.1
      refine ⟨hp.1,hp.2.1,hp.2.2, ?_⟩
      rintro ⟨k,positive,ends⟩
      have eq : shortGapLength lam mu = k :=
        (shortGapRecognition lam mu hp k positive).2.2.mpr ends
      change shortGapLength lam mu = 0 at notShort
      exact (Nat.ne_of_gt positive) (eq.symm.trans notShort)

end LogicLineages.PermittedControl.ActualShortCountCleanup
