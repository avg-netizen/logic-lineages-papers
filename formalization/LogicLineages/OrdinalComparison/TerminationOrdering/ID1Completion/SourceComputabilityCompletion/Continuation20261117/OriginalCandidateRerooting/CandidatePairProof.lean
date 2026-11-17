module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.BoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.CandidatePairProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem reroot (n : Nat) (arity : Fin n → Nat)
    (seed parameter out candidate seedQ targetQ seedType seedRaw : OTerm alpha)
    (q : Request n arity body Delta seed parameter out candidate seedQ targetQ)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)))
    : Nonempty (Derivation body Delta (eqn seedQ targetQ)) := by
  apply OriginalDecodedRank.SupportProof.pairCases candidate _
  intro beta j Theta targetType targetRaw hj ht
  rw [eqnRelabel]
  have q' := RequestRenameProof.rename q j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename] at hs'
  exact BoundsProof.reroot n arity (seed.relabel j) (parameter.relabel j) (out.relabel j) (candidate.relabel j) (seedQ.relabel j) (targetQ.relabel j) (seedType.relabel j) (seedRaw.relabel j) targetType targetRaw q' hs' ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.CandidatePairProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.CandidatePairProof
