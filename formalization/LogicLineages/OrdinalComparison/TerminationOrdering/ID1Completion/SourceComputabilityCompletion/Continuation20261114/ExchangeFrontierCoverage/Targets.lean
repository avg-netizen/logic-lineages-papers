module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal flattened dependencies preserve membership of an actual dependency
of an actual member, with no distinctness or duplicate-removal premise. -/
def InternalFlattenCoverage : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2)
    (frontier node param deps child out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)) →
  Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) out frontier param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child))
/-- Actual original bindList successor, with unchanged depth and dependency
order. This is not an assertion of independently evaluated child/table coherence. -/
def InternalSuccessorCoverage : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2)
    (depth seed param frontier node deps child out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)) →
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) out (suc depth) seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Targets
