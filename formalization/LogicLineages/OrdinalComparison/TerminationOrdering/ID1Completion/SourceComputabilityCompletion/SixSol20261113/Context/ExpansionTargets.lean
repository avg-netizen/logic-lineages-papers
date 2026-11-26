module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixWorkingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261112.Context
/-- The actual original term-job expansion splits at its genuine constructor
arity. Every premise is a literal operational graph, not annotation coherence,
a result invariant, or a supplied suffix identity. Child/deletion order and
all original context coordinates are unchanged. -/
def ActualExpansionSplit : Prop := ∀ (arity : Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (typ raw parameter window gamma rawJob tagged job front suffix jobs annotatedFront mapped full : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tagged typ rawJob)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z tagged)) →
  Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix raw parameter)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs front suffix)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedFront (numeral arity) z typ raw jobs)) →
  Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) mapped suffix typ)) →
  Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion full job)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append full annotatedFront mapped))

/-- The same real source expansion split, together with its actual scalar
suffix iff the unchanged hereditary deletion row at the original packed input.
No prefix scalar correctness or whole runtime completion is claimed. -/
def ActualExpansionDeletionRow : Prop := ∀ (Q : Program 2) (arity : Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw parameter window gamma rawJob tagged job front suffix jobs annotatedFront mapped full row : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tagged typ rawJob)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z tagged)) →
  Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix raw parameter)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs front suffix)) →
  Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedFront (numeral arity) z typ raw jobs)) →
  Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) mapped suffix typ)) →
  Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion full job)) →
  Nonempty (Derivation body Delta
    ((graph2 InternalApplicationValidityStackAppend.append full annotatedFront mapped) ⊓
      ((graph1 (InternalListMap.map (k := 0) (ScheduledDeletionDefinitions.scalarFromJob Q)) row mapped).iff
        (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionTargets
