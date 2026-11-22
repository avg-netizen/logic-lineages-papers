module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoBoundsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (boundBody)
open NumberedWindowInternalChosenAuxMeasureCombineOpenProof (exact_OpenChosenAuxMeasureCombine)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof (boundsRename)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentMemoConsProof (exact_OpenCoverArgumentMemoCons)
open NumberedWindowInternalCoverArgumentMemoGrammarTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem matchCombine (F : Program 1) (h a p mh mt mh' mt' : OTerm α)
    (head : Nonempty (Derivation body Γ (unary F mh h)))
    (head' : Nonempty (Derivation body Γ (unary F mh' h)))
    (tail : Nonempty (Derivation body Γ (unary (argumentMeasure F) mt a)))
    (tail' : Nonempty (Derivation body Γ (unary (argumentMeasure F) mt' a)))
    (combined : Nonempty (Derivation body Γ (programGraph chosenCombine p ![mh,mt]))) :
    Nonempty (Derivation body Γ (programGraph chosenCombine p ![mh',mt'])) := by
  have first := valueUnique F mh mh' ![h] head head'
  have second := valueUnique (argumentMeasure F) mt mt' ![a] tail tail'
  unfold programGraph at combined ⊢
  apply graphInputTransport body α 2 Γ _ p ![mh,mt] ![mh',mt'] _ combined
  intro i
  rw [onEquality]
  exact Fin.cases first (Fin.cases second (fun j => Fin.elim0 j)) i

theorem exact_OpenCoverArgumentMemoBounds : ExactOpenCoverArgumentMemoBounds := by
  intro F body α Γ h a p mh mt dh wh dt wt paid
  let Q := existsOne (boundBody p dh dt wh wt)
  apply exact_OpenCoverArgumentMemoCons F body α Γ h a p Q paid.cons
  intro β j Δ m1 m2 keep actualHead actualTail combined
  have head := renameInto paid.head j Δ keep
  have tail := renameInto paid.tail j Δ keep
  have hp := renameInto paid.headPair j Δ keep
  have tp := renameInto paid.tailPair j Δ keep
  simp only [unaryRename] at head tail
  simp only [pairRename] at hp tp
  have graph := matchCombine F (h.relabel j) (a.relabel j) (p.relabel j)
    m1 m2 (mh.relabel j) (mt.relabel j) actualHead head actualTail tail combined
  change Nonempty (Derivation body Δ ((existsOne (boundBody p dh dt wh wt)).relabel j))
  rw [boundsRename]
  exact exact_OpenChosenAuxMeasureCombine body β Δ (p.relabel j) (mh.relabel j) (mt.relabel j)
    (dh.relabel j) (dt.relabel j) (wh.relabel j) (wt.relabel j) hp tp graph

#print axioms exact_OpenCoverArgumentMemoBounds

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoBoundsProof
