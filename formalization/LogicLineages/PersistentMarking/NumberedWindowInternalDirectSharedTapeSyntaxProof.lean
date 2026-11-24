module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique programRename)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalDirectInsertedScanTargets (scan)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem renamePair (p : Program 2) (out x y : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph p out ![x,y]))) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (programGraph p (out.relabel j) ![x.relabel j,y.relabel j])) := by
  simpa only [programRename,binaryInputsRename] using renameInto h j Δ keep

theorem commonAppend (raw sourceKept targetKept projected joined : OTerm α)
    (ps : Nonempty (Derivation B Γ (unary parser (suc sourceKept) raw)))
    (pt : Nonempty (Derivation B Γ (unary parser (suc targetKept) raw)))
    (ha : Nonempty (Derivation B Γ (programGraph append joined ![targetKept,projected]))) :
    Nonempty (Derivation B Γ (programGraph append joined ![sourceKept,projected])) := by
  obtain ⟨e⟩ := valueUnique parser (suc targetKept) (suc sourceKept) ![raw] pt ps
  unfold programGraph at ha ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula append)
    joined ![targetKept,projected] ![sourceKept,projected] _ ha
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Nonempty (Derivation B Γ (equal targetKept sourceKept))
    rw [equalEqn]
    exact ⟨cancelSuc e⟩
  · obtain rfl := Fin.eq_zero j
    change Nonempty (Derivation B Γ (equal projected projected))
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl projected⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
