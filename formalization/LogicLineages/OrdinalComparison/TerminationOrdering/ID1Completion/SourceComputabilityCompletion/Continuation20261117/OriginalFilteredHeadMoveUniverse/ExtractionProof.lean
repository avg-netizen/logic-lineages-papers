module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.QueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.ExtractionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atValue (raw annotation head tail entries value : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value tail z)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (tailEntries : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) (tail.relabel j) z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  have hn := LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsSupportProof.tailPositive raw annotation head tail entries value hc hex hv
  apply zeroSuccessorCases Delta value _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta tailEntries hj heq
    have hv' := renameInto hv j Theta hj
    simp only [graph2Rename,zRelabel] at hv'
    exact next beta j Theta tailEntries hj
      (outputTransport ArgumentEntriesRecursor.extract (value.relabel j) (suc tailEntries) ![tail.relabel j,z] heq hv')

theorem tailCases (raw annotation head tail entries : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw annotation head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (tailEntries : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) (tail.relabel j) z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases ArgumentEntriesRecursor.extract ![tail,z] _
  intro beta j Theta value hj hv
  have hx : (fun i => (![tail,z] i).relabel j) = ![tail.relabel j,z] := by
    funext i
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun q => Fin.elim0 q) k) i
    · rfl
    · exact zRelabel j
  rw [hx] at hv
  have hc' := renameInto hc j Theta hj
  rw [graph3Rename] at hc'
  have hex' := renameInto hex j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hex'
  apply atValue (raw.relabel j) (annotation.relabel j) (head.relabel j) (tail.relabel j) (entries.relabel j) value _ hc' hex' hv
  intro eta k Xi tailEntries hk he
  have h := next eta (k ∘ j) Xi tailEntries
    (fun q hq => by simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (q.relabel j) (hj q hq))
  have he' : Nonempty (Derivation body Xi (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) (tail.relabel (k ∘ j)) z)) := by
    simpa only [FirstOrder.Language.Term.relabel_relabel] using he
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using h he'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.ExtractionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.ExtractionProof
