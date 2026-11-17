module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.AtFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.TargetBoundsProof
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
    (seed parameter out candidate seedQ targetQ seedType seedRaw targetType targetRaw seedBounds : OTerm alpha)
    (q : Request n arity body Delta seed parameter out candidate seedQ targetQ)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate targetType targetRaw)))
    (hsb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) seedBounds seedRaw)))
    : Nonempty (Derivation body Delta (eqn seedQ targetQ)) := by
  apply InternalAcceptanceSupportProof.programCases (OriginalCodeBoundsRecursion.bounds n)
    (Fin.cons targetRaw Fin.elim0) _
  intro beta j Theta targetBounds hj htb
  rw [eqnRelabel]
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at htb
  have q' := RequestRenameProof.rename q j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [graph1Rename,graph2Rename] at hs'
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename] at ht'
  have hsb' := renameInto hsb j Theta hj
  simp only [graph1Rename,graph2Rename] at hsb'
  exact AtFieldsProof.reroot n arity (seed.relabel j) (parameter.relabel j) (out.relabel j) (candidate.relabel j) (seedQ.relabel j) (targetQ.relabel j) (seedType.relabel j) (seedRaw.relabel j) (targetType.relabel j) (targetRaw.relabel j) (seedBounds.relabel j) targetBounds q' hs' ht' hsb' htb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.TargetBoundsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.TargetBoundsProof
