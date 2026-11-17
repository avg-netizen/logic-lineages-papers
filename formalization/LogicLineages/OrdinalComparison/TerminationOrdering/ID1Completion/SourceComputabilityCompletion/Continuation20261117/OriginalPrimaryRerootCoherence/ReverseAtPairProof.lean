module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.TargetUniverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ParameterOnlyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ReverseAtPairProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationStepPeelSupportProof (andIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem inclusion (n : Nat) (arity : Fin n → Nat)
    (seed parameter typ raw context gamma types out candidate targetOut targetType targetRaw : OTerm alpha)
    (q : OriginalPrimaryRerootInclusion.Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate targetType targetRaw))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included out targetOut)) := by
  have hback := OriginalPrimaryReverseMembership.Proof.reverseMembership n arity body alpha Delta
    seed parameter typ raw context gamma types out candidate targetOut
    q.seedPair q.parameterPair q.guard q.typesGraph q.closed q.accepted q.primary q.member q.targetPrimary
  have ha := TargetUniverseProof.accepted n arity seed parameter typ raw context gamma types out candidate targetOut targetType targetRaw q hp
  have ht := ParameterOnlyProof.types body alpha Delta seed candidate parameter types q.typesGraph
  exact OriginalPrimaryRerootInclusion.Proof.primaryRerootInclusion n arity body alpha Delta
    candidate parameter targetType targetRaw context gamma types targetOut seed out
    hp q.parameterPair q.guard ht q.closed ha q.targetPrimary hback q.primary

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ReverseAtPairProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ReverseAtPairProof
