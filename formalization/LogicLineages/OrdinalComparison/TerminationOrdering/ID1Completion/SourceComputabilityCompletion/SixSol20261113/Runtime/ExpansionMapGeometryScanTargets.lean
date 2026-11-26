module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalAdditionLawsProof (add)
open InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every continuation of the literal annotation scan appends an exact-length
suffix to its earlier row. All roles, types, source rows and counts are arbitrary
internal terms; no source admission, arity restriction or content premise. -/
def ActualExtension : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (start count role typ raw jobs prefixRow full : OTerm alpha),
 Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan prefixRow start role typ raw jobs)) →
 Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add start count) role typ raw jobs)) →
 Nonempty (Derivation body Delta (ExpansionMapGeometryScanDefinitions.Extension count prefixRow full))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanTargets
