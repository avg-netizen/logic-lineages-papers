module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def entry : Program 3 := pairOf (.projection 0) (.projection 1)
def queries : Fin 2 → Program 3 := ![entry,consOf entry (.projection 2)]

theorem atPositive (raw typ head tail entries tailEntries : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (e : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing e (typ.relabel j) (head.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (entries.relabel j) e (tailEntries.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries ![typ,head,tailEntries] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![typ,head,tailEntries] i).relabel j) = ![typ.relabel j,head.relabel j,tailEntries.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  let xs := ![typ.relabel j,head.relabel j,tailEntries.relabel j]
  have hp := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (typ.relabel j) (head.relabel j) xs (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hl := binaryRecover InternalListCodec.consCode entry (.projection 2)
    (ys 1) (ys 0) (tailEntries.relabel j) xs (hq 1) (hq 0) (projectionValue 2 xs)
  have hc' := renameInto hc j Theta hj
  rw [graph3Rename] at hc'
  have he' := renameInto he j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at he' ht'
  have hl' := ExtractionConsSupportProof.entriesCons (raw.relabel j) (typ.relabel j) (head.relabel j)
    (tail.relabel j) (entries.relabel j) (tailEntries.relabel j) (ys 0) (ys 1) hc' he' ht' hp hl
  exact next beta j Theta (ys 0) hj hp hl'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
