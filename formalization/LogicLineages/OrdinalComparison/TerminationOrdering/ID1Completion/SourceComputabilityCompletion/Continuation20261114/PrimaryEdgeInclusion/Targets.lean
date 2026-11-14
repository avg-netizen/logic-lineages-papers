module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership

/-- Genuine arbitrary-list internal existential introduction into the actual
anyEdge fold, from an actual member and an actual exact-one edge graph. -/
def AnyIntroduction : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (reached source candidate parameter : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached source)) →
  Nonempty (Derivation body Delta (graph3 E (numeral 1) source candidate parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.anyEdge E) (numeral 1) reached candidate parameter))

/-- Actual ordered-filter inclusion on arbitrary symbolic pool, testing the
SAME old reached at each entry. No native list semantics enter the premise. -/
def FilterIntroduction : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (pool reached candidate parameter filtered : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool candidate)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.anyEdge E) (numeral 1) reached candidate parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.filterReached E) filtered pool reached parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) filtered candidate))

/-- Right-side membership in the existing actual append, complementing the
already checked left preservation. All list codes remain runtime terms. -/
def AppendRightMembership : Prop := ∀ (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (left right out needle : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 InternalApplicationValidityStackAppend.append out left right)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) right needle)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle))

/-- Actual one-step reachability growth: an internally witnessed accepted
edge from an old reached member to a pool member adds that candidate.
E correctness is NOT supplied by native calibration or asserted here. -/
def ExpansionEdgeInclusion : Prop := ∀ (E : Program 3) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (pool reached source candidate parameter out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached source)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool candidate)) →
  Nonempty (Derivation body Delta (graph3 E (numeral 1) source candidate parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (PrimaryExpansion.expand E) out pool reached parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.Targets
