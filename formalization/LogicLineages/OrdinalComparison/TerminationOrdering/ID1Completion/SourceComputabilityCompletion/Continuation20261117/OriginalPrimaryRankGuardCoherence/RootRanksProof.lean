module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.GuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.MinimumMemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.RootRanksProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem sameRank (n : Nat) (arity : Fin n → Nat)
 (seed parameter typ raw out minimumOut minimumType minimumRaw seedRank minimumRank : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ raw)))
 (had : Nonempty (Derivation body Delta (graph2 (T n arity) (numeral 1) seed parameter)))
 (hl : Nonempty (Derivation body Delta (graph2 (L n arity) out seed parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 (R n arity) minimumOut seed parameter)))
 (hmp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing minimumOut minimumType minimumRaw)))
 (hsr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw seedRank seed)))
 (hmr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw minimumRank minimumOut)))
 : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.sameRank (R n arity)) (numeral 1) seed parameter)) := by
 have hmem := MinimumMemberProof.member (T n arity) (Q n arity) (E n arity) seed parameter out minimumOut had hl hm
 have heq := OriginalPrimaryVariableRankPreservation.Proof.primaryVariableRankPreservation n arity body alpha Delta seed parameter out minimumOut typ raw minimumType minimumRaw seedRank minimumRank hp hmp hsr hmr had hl hmem
 exact GuardProof.sameRank (R n arity) seed parameter minimumOut seedRank minimumRank hm hsr hmr heq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.RootRanksProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.RootRanksProof
