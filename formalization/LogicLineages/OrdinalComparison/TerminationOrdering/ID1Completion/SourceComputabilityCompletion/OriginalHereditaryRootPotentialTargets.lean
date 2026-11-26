module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
/-- Exact initial agenda potential equals the literal computed runtime fuel.
The fixed branching comes from the actual root branching Program (weight+2),
not an externally chosen standard natural bound. No source/evaluator claim. -/
def ActualInitialPotential : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent visit work branching fuel : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit z parent)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit z)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching branching parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.fuel fuel parent)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda fuel work branching))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialTargets
