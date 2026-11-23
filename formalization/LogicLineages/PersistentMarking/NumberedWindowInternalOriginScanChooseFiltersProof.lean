module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanChooseFiltersProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalRawListRecursion (listRec recGraph)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep zeroBase)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalOriginScanInductionTargets (Pools)
open NumberedWindowInternalOriginScanInductionSyntaxProof (renamePools)
open NumberedWindowInternalOriginScanInductionProof (exact_OpenOriginScanAtRows)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem filterOfPair (side : Bool) (out code pool : OTerm α)
    (f : Nonempty (Derivation B Γ (programGraph (listRec zeroBase (rowStep side)) out ![code,pool]))) :
    Nonempty (Derivation B Γ (filterGraph side out code pool)) := by
  have e : (![code,pool] : Fin 2 → OTerm α) = Fin.cons code (![pool] : Fin 1 → OTerm α) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  simpa only [filterGraph,recGraph,e] using f

/-- Choose the actual two ordered filter outputs and prove both side
scans. All row witnesses are carried by the original scanner. -/
theorem exact_OriginalChooseCertifiedFilters (r : Program 3)
    (rows removed decoded rawL rawR scratchL scratchR joined : OTerm α) (goal : Formula α)
    (p : Pools B Γ removed decoded rawL rawR scratchL scratchR joined)
    (accepted : Nonempty (Derivation B Γ (loopAccept r rows removed)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (outL outR : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (filterGraph true outL (rows.relabel j) (scratchL.relabel j))) →
      Nonempty (Derivation B Δ (filterGraph false outR (rows.relabel j) (scratchL.relabel j))) →
      Nonempty (Derivation B Δ (loopAccept r outL (rawL.relabel j))) →
      Nonempty (Derivation B Δ (loopAccept r outR (rawR.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  let F := listRec zeroBase (rowStep true)
  let G := listRec zeroBase (rowStep false)
  apply programCases F ![rows,scratchL] goal
  intro β j Δ l keep lf
  rw [binaryInputsRename] at lf
  apply programCases G ![rows.relabel j,scratchL.relabel j] (goal.relabel j)
  intro γ k Ω outR carry rf
  rw [binaryInputsRename] at rf
  let ρ := k ∘ j
  have keep' := keepThrough j k keep carry
  have pack := renamePools p ρ keep'
  have l' := renamePair F l (rows.relabel j) (scratchL.relabel j) lf k carry
  have af := renameInto accepted ρ Ω keep'
  rw [loopRename] at af
  let outL := l.relabel k
  have fL : Nonempty (Derivation B Ω (filterGraph true outL (rows.relabel ρ) (scratchL.relabel ρ))) := by
    apply filterOfPair
    simpa only [F,ρ,outL,← Term.relabel_relabel] using l'
  have fR : Nonempty (Derivation B Ω (filterGraph false outR (rows.relabel ρ) (scratchL.relabel ρ))) := by
    apply filterOfPair
    simpa only [G,ρ,← Term.relabel_relabel] using rf
  obtain ⟨sides⟩ := exact_OpenOriginScanAtRows r B γ Ω (rows.relabel ρ) (removed.relabel ρ)
    (decoded.relabel ρ) (rawL.relabel ρ) (rawR.relabel ρ) (scratchL.relabel ρ) (scratchR.relabel ρ)
    (joined.relabel ρ) outL outR pack af fL fR
  rw [formulaRelabelComposition j k goal]
  exact next γ ρ Ω outL outR keep' fL fR
    ⟨Derivation.conjunctionLeft sides⟩ ⟨Derivation.conjunctionRight sides⟩

#print axioms exact_OriginalChooseCertifiedFilters
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanChooseFiltersProof
