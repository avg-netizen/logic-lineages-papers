module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityCasesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertion
open OriginalInternalIndexedPrefixCasesTargets (bump)
def First (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (psi : Formula alpha)
 (raw parameter index child : OTerm alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (arity : Nat),
 (arity = 1 ∨ arity = 2) →
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) (raw.relabel j) (parameter.relabel j))) →
 Nonempty (Derivation body Theta (eqn (index.relabel j) z)) →
 Nonempty (Derivation body Theta (graph2 OriginalHereditaryExpansion.firstJob (child.relabel j) (raw.relabel j) (parameter.relabel j))) →
 Nonempty (Derivation body Theta (psi.relabel j))
def Second (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (psi : Formula alpha)
 (raw parameter index child : OTerm alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) (raw.relabel j) (parameter.relabel j))) →
 Nonempty (Derivation body Theta (eqn (index.relabel j) (suc z))) →
 Nonempty (Derivation body Theta (graph2 OriginalHereditaryExpansion.secondJob (child.relabel j) (raw.relabel j) (parameter.relabel j))) →
 Nonempty (Derivation body Theta (psi.relabel j))
def Deleted (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (psi : Formula alpha)
 (raw parameter index child : OTerm alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (arity : Nat) (row cutoff count : OTerm beta),
 (arity = 0 ∨ arity = 1 ∨ arity = 2) →
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) (raw.relabel j) (parameter.relabel j))) →
 Nonempty (Derivation body Theta (eqn (index.relabel j) (bump arity cutoff))) →
 Nonempty (Derivation body Theta (graph2 OriginalHereditaryExpansion.deletionJobs row (raw.relabel j) (parameter.relabel j))) →
 Nonempty (Derivation body Theta (lengthGraph count row)) →
 Nonempty (Derivation body Theta (Below cutoff count)) →
 Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup (child.relabel j) cutoff row)) →
 Nonempty (Derivation body Theta (psi.relabel j))
def ActualCases : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw parameter jobs count index child : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
 Nonempty (Derivation body Delta (lengthGraph count jobs)) →
 Nonempty (Derivation body Delta (Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index jobs)) →
 First body Delta psi raw parameter index child →
 Second body Delta psi raw parameter index child →
 Deleted body Delta psi raw parameter index child →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupTargets
