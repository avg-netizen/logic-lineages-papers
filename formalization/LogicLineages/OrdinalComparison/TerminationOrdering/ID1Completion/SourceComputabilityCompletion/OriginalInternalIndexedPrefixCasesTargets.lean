module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn z suc)
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion

def bump {alpha : Type} : Nat → OTerm alpha → OTerm alpha
 | 0, t => t
 | n+1, t => suc (bump n t)

def Head (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (psi : Formula alpha) (original value head : OTerm alpha) (offset : Nat) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (eqn (original.relabel j) (bump offset z))) →
 Nonempty (Derivation body Theta (eqn (value.relabel j) (head.relabel j))) →
 Nonempty (Derivation body Theta (psi.relabel j))
def Tail (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (psi : Formula alpha) (original value suffix : OTerm alpha) (offset : Nat) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (index count : OTerm beta),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (eqn (original.relabel j) (bump offset index))) →
 Nonempty (Derivation body Theta (lengthGraph count (suffix.relabel j))) →
 Nonempty (Derivation body Theta (Below index count)) →
 Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup (value.relabel j) index (suffix.relabel j))) →
 Nonempty (Derivation body Theta (psi.relabel j))
def Unary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (front first suffix joined count index value : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (consGraph front first z)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)) →
 Nonempty (Derivation body Delta (lengthGraph count joined)) →
 Nonempty (Derivation body Delta (Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index joined)) →
 Head body Delta psi index value first 0 → Tail body Delta psi index value suffix 1 → Nonempty (Derivation body Delta psi)
def Binary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (front first middle second suffix joined count index value : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (consGraph front first middle)) →
 Nonempty (Derivation body Delta (consGraph middle second z)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)) →
 Nonempty (Derivation body Delta (lengthGraph count joined)) →
 Nonempty (Derivation body Delta (Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index joined)) →
 Head body Delta psi index value first 0 → Head body Delta psi index value second 1 → Tail body Delta psi index value suffix 2 →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesTargets
