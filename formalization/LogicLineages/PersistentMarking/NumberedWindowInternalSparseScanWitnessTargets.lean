module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedSeen

/-- A particular genuine prior member, equal to the candidate or related by
an accepting directed edge, suffices to make this original scan succeed. -/
def ExactWitnessRowAcceptance : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (seen ctx ty w k : OTerm α),
    Nonempty (Derivation body Γ ((witnessRow E seen ctx ty w k).imp (scanGraph E seen ctx ty k)))

/-- The same existential uses an actual seen member, with both equality and
edge alternatives at that very member. No witness is a parameter. -/
def ExactOpenScanWitnessEquivalence : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (seen ctx ty k : OTerm α),
    let scan := scanGraph E seen ctx ty k
    let witness := seenWitness E seen ctx ty k
    Nonempty (Derivation body Γ ((scan.imp witness) ⊓ (witness.imp scan)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessTargets
