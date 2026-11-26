module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership

/-- No spurious acceptance: actual any fold acceptance exposes an actual
old-list member with actual E acceptance, inside the original calculus. -/
def AnyWitness : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (reached candidate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.anyEdge E) (numeral 1) reached candidate parameter)) →
  Nonempty (Derivation body Delta (sourceWitness E reached candidate parameter))

/-- Exact filter membership soundness; tested reached remains the old list. -/
def FilterSoundness : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (pool reached parameter filtered candidate : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.filterReached E) filtered pool reached parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) filtered candidate)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool candidate ⊓
    graph3 (PrimaryExpansion.anyEdge E) (numeral 1) reached candidate parameter))

/-- Internal disjunction of actual input memberships, complementing both
already checked append introduction directions. -/
def AppendSoundness : Prop := ∀ (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (left right out candidate : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 InternalApplicationValidityStackAppend.append out left right)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) left candidate ⊔
    graph2 contains (numeral 1) right candidate))

/-- Exact literal one-step membership characterization, with the newly
reached branch carrying a genuine internal existential edge witness.
This does not claim semantic correctness of arbitrary E or cutoff closure. -/
def ExpansionCharacterization : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (pool reached parameter out candidate : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) out pool reached parameter)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) ↔
   Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached candidate ⊔
     (graph2 contains (numeral 1) pool candidate ⊓ sourceWitness E reached candidate parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Targets
