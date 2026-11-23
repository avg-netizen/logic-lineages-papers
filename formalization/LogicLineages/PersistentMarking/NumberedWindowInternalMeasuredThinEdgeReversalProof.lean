module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalOptionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScalarEdge (exchangeTape edge4)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (compareOptions guardedExchange)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (swapExchange pairedExchange)
open NumberedWindowInternalMeasuredThinEdgeReversalTargets
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OptionReversal : ExactOptionReversal :=
  NumberedWindowInternalMeasuredThinEdgeReversalOptionProof.reverseOptions

private theorem swapGraphs (X : Program 2) (a b : OTerm α) :
    Nonempty (Derivation body Γ (programGraph (swapExchange X) (suc z) (exchangeTape a b))) ↔
      Nonempty (Derivation body Γ (programGraph X (suc z) (exchangeTape b a))) := by
  let xs := exchangeTape a b
  let ys := exchangeTape b a
  let ps : Fin 2 → Program 2 := ![.projection 1,.projection 0]
  have projections (i : Fin 2) : Nonempty (Derivation body Γ (programGraph (ps i) (ys i) xs)) :=
    Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 0 xs) (fun k => Fin.elim0 k)) i
  exact ⟨fun h => compositionRecover X ps (suc z) xs ys h projections,
    fun h => compositionValue X ps (suc z) xs ys h projections⟩

theorem exact_PairedEdgeReversal : ExactPairedEdgeReversal := by
  intro C s baseX W body α Γ ctx ty a b
  let pair := pairedExchange baseX
  let X := guardedExchange C s pair
  let edge := acceptEdge (edge4 X W) ctx ty a b
  let Δ := edge :: Γ
  have h : Derivation body Δ edge := Derivation.hypothesis List.mem_cons_self
  obtain ⟨fwd⟩ := NumberedWindowInternalSparseScalarEdgeOpenChecks.exact_OpenPackedScalarEdge X W body α Δ ctx ty a b
  obtain ⟨back⟩ := NumberedWindowInternalSparseScalarEdgeOpenChecks.exact_OpenPackedScalarEdge X W body α Δ ctx ty b a
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft fwd) h
  obtain ⟨guards⟩ := conjunctionRecover pair (compareOptions C s) (exchangeTape a b) ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨both⟩ := conjunctionRecover baseX (swapExchange baseX) (exchangeTape a b) ⟨Derivation.conjunctionLeft guards⟩
  have swapped := conjunctionAccept baseX (swapExchange baseX) (exchangeTape b a)
    ((swapGraphs baseX a b).mp ⟨Derivation.conjunctionRight both⟩)
    ((swapGraphs baseX b a).mpr ⟨Derivation.conjunctionLeft both⟩)
  obtain ⟨cmp⟩ := exact_OptionReversal C s body α Δ a b
  obtain ⟨accept⟩ := conjunctionAccept pair (compareOptions C s) (exchangeTape b a) swapped
    ⟨Derivation.implicationElimination cmp (Derivation.conjunctionRight guards)⟩
  let wins := Derivation.conjunctionRight calls
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (Derivation.conjunctionRight back)
    (Derivation.conjunctionIntroduction accept (Derivation.conjunctionIntroduction
      (Derivation.conjunctionRight wins) (Derivation.conjunctionLeft wins))))⟩

#print axioms exact_PairedEdgeReversal
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalProof
