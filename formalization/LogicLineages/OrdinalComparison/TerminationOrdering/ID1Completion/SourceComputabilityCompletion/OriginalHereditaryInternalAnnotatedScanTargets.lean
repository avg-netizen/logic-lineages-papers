module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion
/-- Bounded lookup in the actual annotation scan is the actual indexed cell. -/
def Indexed : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count role typ raw jobs output index child : OTerm alpha),
 Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan output count role typ raw jobs)) →
 Nonempty (Derivation body Delta (Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index output)) →
 Nonempty (Derivation body Delta (graph5 OriginalHereditaryInternalAnnotatedScanDefinitions.cell child index role typ raw jobs))
/-- The raw job and original raw-row length are queried internally; no raw
lookup, raw bound, source validity or native typing premise is supplied. -/
def ActualLookup : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (role typ raw jobs output count index child : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll output role typ raw jobs)) →
 Nonempty (Derivation body Delta (lengthGraph count output)) →
 Nonempty (Derivation body Delta (Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index output)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (rawChild : OTerm beta),
   (∀ p ∈ Delta, p.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (lengthGraph (count.relabel j) (jobs.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup rawChild (index.relabel j) (jobs.relabel j))) →
   Nonempty (Derivation body Theta (graph5 OriginalHereditaryAnnotatedExpansion.decorate (child.relabel j)
     (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) rawChild)) →
   Nonempty (Derivation body Theta (psi.relabel j))) → Nonempty (Derivation body Delta psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanTargets
