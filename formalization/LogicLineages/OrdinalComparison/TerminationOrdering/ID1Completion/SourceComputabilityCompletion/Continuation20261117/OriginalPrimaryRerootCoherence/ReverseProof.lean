module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ReverseAtPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.RequestRenameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ReverseProof
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
    (seed parameter typ raw context gamma types out candidate targetOut : OTerm alpha)
    (q : OriginalPrimaryRerootInclusion.Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included out targetOut)) := by
  apply OriginalDecodedRank.SupportProof.pairCases candidate _
  intro beta j Theta targetType targetRaw hj hp
  rw [PrimaryMonotonicity.InclusionProof.includedRename]
  have q' := OriginalPrimaryRerootInclusion.RequestRenameProof.rename q j Theta hj
  exact ReverseAtPairProof.inclusion n arity (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) (candidate.relabel j) (targetOut.relabel j) targetType targetRaw q' hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ReverseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ReverseProof
