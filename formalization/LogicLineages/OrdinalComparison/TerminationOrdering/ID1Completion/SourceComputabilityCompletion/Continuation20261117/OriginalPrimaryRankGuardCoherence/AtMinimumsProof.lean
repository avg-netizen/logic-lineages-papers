module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.RootPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.RequestRenameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.AtMinimumsProof
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
attribute [local irreducible] OriginalConcreteHeadSignature.signature OriginalCandidates.candidates OriginalDecodedContextValidity.contextGuard OriginalConcreteStructuralEdge.edge SeededPrimaryPool.pool
theorem coherent (n : Nat) (arity : Fin n → Nat) (source : Program 2) (window : Program 1)
 (seed parameter typ raw context gamma types out candidate targetOut guardedOut targetGuardedOut minimumOut targetMinimumOut candidateType candidateRaw : OTerm alpha)
 (q : OriginalPrimaryRerootInclusion.Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut)
 (hg : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.representative source (R n arity) window) guardedOut seed parameter)))
 (htg : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.representative source (R n arity) window) targetGuardedOut candidate parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 (R n arity) minimumOut seed parameter)))
 (htm : Nonempty (Derivation body Delta (graph2 (R n arity) targetMinimumOut candidate parameter)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate candidateType candidateRaw)))
 : Nonempty (Derivation body Delta (equal guardedOut targetGuardedOut)) := by
 have had := OriginalPrimaryRerootInclusion.AdmissionProof.both n arity seed parameter typ raw context gamma types out candidate targetOut q
 have hs := RootPairProof.sameRank n arity seed parameter typ raw out minimumOut q.seedPair had.1 q.primary hm
 have ht := RootPairProof.sameRank n arity candidate parameter candidateType candidateRaw targetOut targetMinimumOut hcp had.2 q.targetPrimary htm
 have he1 := GuardProof.output source (R n arity) window seed parameter minimumOut guardedOut hm hs hg
 have he2 := GuardProof.output source (R n arity) window candidate parameter targetMinimumOut targetGuardedOut htm ht htg
 have hem := OriginalPrimaryMinimumCoherence.Proof.minimumCoherence n arity body alpha Delta seed parameter typ raw context gamma types out candidate targetOut minimumOut targetMinimumOut q.seedPair q.parameterPair q.guard q.typesGraph q.closed q.accepted q.primary q.member q.targetPrimary hm htm
 rw [equalEqn] at hem ⊢
 obtain ⟨he1⟩ := he1
 obtain ⟨he2⟩ := he2
 obtain ⟨hem⟩ := hem
 exact ⟨InternalTagArithmeticSupportProof.trans (InternalTagArithmeticSupportProof.trans he1 hem) (InternalTagArithmeticSupportProof.symm he2)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.AtMinimumsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.AtMinimumsProof
