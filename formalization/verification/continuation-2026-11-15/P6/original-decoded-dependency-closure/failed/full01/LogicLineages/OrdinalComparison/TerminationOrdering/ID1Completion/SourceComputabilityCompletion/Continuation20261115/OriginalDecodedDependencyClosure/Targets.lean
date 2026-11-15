module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- A genuinely accepted original code has accepted actual immediate children at
their own raw+1/raw cutoffs. No typed constructor/image or positional witness. -/
def InternalChildrenClosed : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw children child : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) →
  Nonempty (Derivation body Delta (graph1 Continuation20261114.ArgumentEntriesChildren.children children raw)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) children child)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child))
/-- Membership in the concrete original decoded dependency output itself forces
both child coordinates valid. Parent guard success and both parent coordinates
are reconstructed internally; they are not public premises. -/
def InternalDependenciesClosed : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (node parameter out child childLeft childRight : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) out node parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childLeft childRight)) →
  Nonempty (Derivation body Delta
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) childLeft ⊓
     graph1 (OriginalCodeValidityGuard.check n) (numeral 1) childRight))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.Targets
