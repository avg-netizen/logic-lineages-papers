module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.CandidatePairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.Proof
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
    (seed parameter out candidate seedQ targetQ : OTerm alpha)
    (q : Request n arity body Delta seed parameter out candidate seedQ targetQ)
    : Nonempty (Derivation body Delta (eqn seedQ targetQ)) := by
  apply OriginalDecodedRank.SupportProof.pairCases seed _
  intro beta j Theta seedType seedRaw hj hs
  rw [eqnRelabel]
  have q' := RequestRenameProof.rename q j Theta hj
  exact CandidatePairProof.reroot n arity (seed.relabel j) (parameter.relabel j) (out.relabel j) (candidate.relabel j) (seedQ.relabel j) (targetQ.relabel j) seedType seedRaw q'  hs

theorem candidateRerooting : Targets.InternalCandidateRerooting := by
  intro n arity body alpha Delta seed parameter out candidate seedQ targetQ had hl hm hs ht
  exact reroot n arity seed parameter out candidate seedQ targetQ ⟨had,hl,hm,hs,ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.Proof
