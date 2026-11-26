module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.RootRanksProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.RootMinimumRankProof
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
 (seed parameter typ raw out minimumOut minimumType minimumRaw seedRank : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ raw)))
 (had : Nonempty (Derivation body Delta (graph2 (T n arity) (numeral 1) seed parameter)))
 (hl : Nonempty (Derivation body Delta (graph2 (L n arity) out seed parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 (R n arity) minimumOut seed parameter)))
 (hmp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing minimumOut minimumType minimumRaw)))
 (hsr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw seedRank seed)))
 : Nonempty (Derivation body Delta (graph2 (OriginalRankGuardedRepresentative.sameRank (R n arity)) (numeral 1) seed parameter)) := by
 apply programCases OriginalRawSyntaxTransport.variableRankPackedRaw (Fin.cons minimumOut Fin.elim0) _
 intro beta j Theta minimumRank hj hnew
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hnew
 simp only [graph2Rename,numeral,sucRelabel,zRelabel]
 have hp' := renameInto hp j Theta hj
 simp only [graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel] at hp'
 have had' := renameInto had j Theta hj
 simp only [graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel] at had'
 have hl' := renameInto hl j Theta hj
 simp only [graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel] at hl'
 have hm' := renameInto hm j Theta hj
 simp only [graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel] at hm'
 have hmp' := renameInto hmp j Theta hj
 simp only [graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel] at hmp'
 have hsr' := renameInto hsr j Theta hj
 simp only [graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel] at hsr'
 exact RootRanksProof.sameRank n arity (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (out.relabel j) (minimumOut.relabel j) (minimumType.relabel j) (minimumRaw.relabel j) (seedRank.relabel j) minimumRank hp' had' hl' hm' hmp' hsr' hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.RootMinimumRankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.RootMinimumRankProof
