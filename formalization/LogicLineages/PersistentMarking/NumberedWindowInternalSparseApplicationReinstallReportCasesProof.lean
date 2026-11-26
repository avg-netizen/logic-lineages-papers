module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallResultProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallReportCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
  (reportBody reportBinder reportUnfold reportRename)
open NumberedWindowInternalSparseApplicationReinstallResultProof (sameResult)

attribute [local irreducible] programGraph

private theorem addressRename {α β : Type} (c e k : OTerm α) (j : α → β) :
    (addressTerm c e k).relabel j = addressTerm (c.relabel j) (e.relabel j) (k.relabel j) := by
  simp only [addressTerm,consTerm,pairTerm,addRelabel,mulRelabel,sucRelabel,zRelabel,numeralRename]

private theorem bodyRename {α β : Type} (least : Program 3) (c e raw y k : OTerm α) (j : α → β) :
    (reportBody least c e raw y k).relabel j =
      reportBody least (c.relabel j) (e.relabel j) (raw.relabel j) (y.relabel j) (k.relabel j) := by
  simp only [reportBody,conjunctionRename,graph3Rename,sucRelabel,eqnRelabel,addressRename]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem casesReport (least : Program 3) (c e raw y : OTerm α) (goal : Formula α)
    (report : Nonempty (Derivation body Γ (outputReport least c e raw y)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (k : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (reportBody least (c.relabel j) (e.relabel j) (raw.relabel j) (y.relabel j) k)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  rw [reportUnfold] at report
  obtain ⟨existence⟩ := report
  let j : α → α ⊕ Fin 1 := Sum.inl
  let matrix := reportBinder least c e raw y
  let Δ := matrix :: Γ.map weaken
  have available (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have current : Nonempty (Derivation body Δ matrix) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := next (α ⊕ Fin 1) j Δ (.var (.inr 0)) available current
  exact ⟨Derivation.existentialElimination existence result⟩

/-- Open both genuine class binders while reusing exactly the same input
triple. The original external calibration is not a premise. -/
theorem coherent (least : Program 3) (c e raw y w : OTerm α)
    (left : Nonempty (Derivation body Γ (outputReport least c e raw y)))
    (right : Nonempty (Derivation body Γ (outputReport least c e raw w))) :
    Nonempty (Derivation body Γ (eqn y w)) := by
  apply casesReport least c e raw y (eqn y w) left
  intro β j Δ k keep src
  rw [eqnRelabel]
  have dst := renameInto right j Δ keep
  rw [reportRename] at dst
  apply casesReport least (c.relabel j) (e.relabel j) (raw.relabel j) (w.relabel j)
    (eqn (y.relabel j) (w.relabel j)) dst
  intro γ μ Ξ l still dest
  rw [eqnRelabel]
  have moved := renameInto src μ Ξ still
  rw [bodyRename] at moved
  exact sameResult least ((c.relabel j).relabel μ) ((e.relabel j).relabel μ)
    ((raw.relabel j).relabel μ) ((y.relabel j).relabel μ) ((w.relabel j).relabel μ)
    (k.relabel μ) l moved dest

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallReportCasesProof
