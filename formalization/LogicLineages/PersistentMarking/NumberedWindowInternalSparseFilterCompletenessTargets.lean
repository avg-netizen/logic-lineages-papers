module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterRetentionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- Every scanned member of the original input vertices occurs in the
actual filtered output on precisely that tape and test program. -/
def ExactScannedMemberRetention : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out vertices seen ctx ty k : OTerm α),
    Nonempty (Derivation body Γ ((passGraph E out vertices seen ctx ty ⊓
      (memberGraph vertices k ⊓ scanGraph E seen ctx ty k)).imp (memberGraph out k)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessTargets
