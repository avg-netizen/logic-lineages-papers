module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallRowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion
def BoundedCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (row head tail count index value : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (consGraph row head tail)) →
 Nonempty (Derivation body Delta (lengthGraph count row)) →
 Nonempty (Derivation body Delta (Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index row)) →
 (∀ (Theta : List (Formula alpha)), (∀ f ∈ Delta, f ∈ Theta) →
   Nonempty (Derivation body Theta (eqn value head)) → Nonempty (Derivation body Theta psi)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (pred tailCount : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (lengthGraph tailCount (tail.relabel j))) →
   Nonempty (Derivation body Theta (Below pred tailCount)) →
   Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup (value.relabel j) pred (tail.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixTargets
