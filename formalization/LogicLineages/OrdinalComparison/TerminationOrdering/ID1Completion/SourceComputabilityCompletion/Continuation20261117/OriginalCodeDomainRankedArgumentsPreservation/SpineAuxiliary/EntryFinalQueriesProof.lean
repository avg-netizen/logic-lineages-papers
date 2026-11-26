module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.EntryFinalQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Continuation20261114
def old : Program 2 := .composition ArgumentEntriesRecursor.graph ![.projection 0,.projection 0,.projection 1]
def dependencies : Program 2 := ArgumentEntriesRecursor.dependency
def answers : Program 2 := .composition ExchangeMapGraph.mapGraph ![dependencies,old]
def queries : Fin 3 → Program 2 := ![old,dependencies,answers]

theorem recover (raw param : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![raw,param]))) :
    Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph (ys 0) raw raw param)) ∧
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency (ys 1) raw param)) ∧
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph (ys 2) (ys 1) (ys 0))) := by
  exact ⟨InternalOriginalUniformVertexPathSupportProof.ternaryRecover ArgumentEntriesRecursor.graph
    (.projection 0) (.projection 0) (.projection 1) (ys 0) raw raw param ![raw,param]
    (hq 0) (projectionValue 0 ![raw,param]) (projectionValue 0 ![raw,param]) (projectionValue 1 ![raw,param]),
    hq 1,binaryRecover ExchangeMapGraph.mapGraph dependencies old (ys 2) (ys 1) (ys 0) ![raw,param] (hq 2) (hq 1) (hq 0)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.EntryFinalQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.EntryFinalQueriesProof
