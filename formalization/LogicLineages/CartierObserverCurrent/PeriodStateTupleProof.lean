module
public import LogicLineages.OrdinalComparison.CartierOrbitDefinitions
import LogicLineages.CartierObserverCurrent.PeriodLaurentBridgeStatementChecks
import LogicLineages.CartierObserverCurrent.PeriodTupleExistenceProof
public meta import LogicLineages.Audit
public section
namespace LogicLineages.CartierObserverCurrent.PeriodStateTuple
open LogicLineages.OrdinalComparison

/-- A single coincidence of two actual whole rational differential states
forces the actual residue tuple to be Frobenius-periodic with the same
shift. Coefficient -1 of the genuine translated Laurent embedding is
applied to the equality of states; the checked iterated-residue and
initial-residue laws identify both sides, and inverse Frobenius is
cancelled. No observation, regularity or transport premise. -/
theorem statePeriodic (u : Nat) (hu : 5 ≤ u) (j p : Nat)
    (hstates :
      (actualDifferentialCartier (K := ActualResidueField))^[j + p] (actualLinkedDifferential u) =
        (actualDifferentialCartier (K := ActualResidueField))^[j] (actualLinkedDifferential u)) :
    Function.IsPeriodicPt (actualResidueTupleFrobenius u) p (actualResidueTuple u) := by
  funext z
  rw [PeriodTupleFacts.actualIterate]
  have h := congrArg (fun f : RatFunc ActualResidueField =>
    (actualTranslatedRationalEmbedding z.val f).coeff (-1)) hstates
  rw [PeriodLaurentBridge.StatementChecks.fixed_iteratedResidue,
    PeriodLaurentBridge.StatementChecks.fixed_iteratedResidue,
    PeriodLaurentBridge.StatementChecks.fixed_initialResidue u hu z,
    iterateFrobeniusEquiv_symm_add_apply] at h
  have hp := (iterateFrobeniusEquiv ActualResidueField 2 j).symm.injective h
  have hforward := congrArg (iterateFrobeniusEquiv ActualResidueField 2 p) hp
  simp only [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def] at hforward
  exact hforward.symm

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodStateTuple
end LogicLineages.CartierObserverCurrent.PeriodStateTuple
