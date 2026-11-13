module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineChildrenTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalUniverseDecoderInternalAcceptance OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Genuine two-way source-admission elimination. The caller supplies no tag
split or child acceptance. Every impossible raw tag is eliminated internally.
The callbacks retain actual constructors and original checker facts, with a
strict internal raw-tail bound for subsequent arithmetic strong induction. -/
def ActualCases : Prop := ∀ (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (types raw gamma c : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (ArgumentsAccepted H M W types raw gamma c)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (programGraph OriginalRawSyntaxTransport.nilConstructor (raw.relabel j) Fin.elim0)) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
    (domain head tail requestedDomain tailTypes : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.consConstructor (raw.relabel j) domain head tail)) →
   Nonempty (Derivation body Theta (StepArrowFields (types.relabel j) requestedDomain tailTypes)) →
   Nonempty (Derivation body Theta (TermAccepted H M W domain head (gamma.relabel j) (c.relabel j))) →
   Nonempty (Derivation body Theta (ArgumentsAccepted H M W tailTypes tail (gamma.relabel j) (c.relabel j))) →
   Nonempty (Derivation body Theta (InternalLessThan.strictLess tail (raw.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesTargets
