module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterRetentionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterRetentionChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseDirectedFilter (cell passGraph pass passTape restRow)
open NumberedWindowInternalSparseDirectedFilterOpenChecks (exact_OpenDirectedFilterCons)
open NumberedWindowInternalSparseDirectedFilterOpenSyntaxProof (reportBinder)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalSparseFilterRetentionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem reportCases (E : Program 4) (vertices h tail seen ctx ty out : OTerm α)
    (goal : Formula α) (input : Derivation body Γ (cell vertices h tail ⊓ passGraph E out vertices seen ctx ty))
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (rest : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Derivation body Δ (restRow E (out.relabel j) (h.relabel j) (tail.relabel j) rest
        (seen.relabel j) (ctx.relabel j) (ty.relabel j)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let row := reportBinder E out h tail seen ctx ty
  let Δ := row :: Γ.map weaken
  obtain ⟨rule⟩ := exact_OpenDirectedFilterCons E body α Γ vertices h tail seen ctx ty out
  have report : Derivation body Γ (existsOne row) := Derivation.implicationElimination rule input
  obtain ⟨result⟩ := each _ j Δ (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)) (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.existentialElimination report result⟩

private theorem headRow (E : Program 4) (h out rest seen ctx ty : OTerm α)
    (scan : Derivation body Γ (scanGraph E seen ctx ty h))
    (choice : Derivation body Γ ((scanGraph E seen ctx ty h ⊓ cell out h rest) ⊔
      ((scanGraph E seen ctx ty h).not ⊓ eqn out rest))) :
    Nonempty (Derivation body Γ (memberGraph out h)) := by
  let L := scanGraph E seen ctx ty h ⊓ cell out h rest
  let R := (scanGraph E seen ctx ty h).not ⊓ eqn out rest
  have l : Derivation body (L :: Γ) L := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hit⟩ := headMember out h rest h ⟨Derivation.conjunctionRight l⟩ ⟨refl h⟩
  have r : Derivation body (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
  have no := Derivation.implicationElimination (Derivation.conjunctionLeft r) (addHyp scan R)
  exact ⟨disjunctionElimination choice (Derivation.implicationIntroduction hit)
    (Derivation.implicationIntroduction (Derivation.explosion no))⟩

theorem exact_ScannedHeadRetained : ExactScannedHeadRetained := by
  intro E body α Γ vertices h tail seen ctx ty out
  let A := (cell vertices h tail ⊓ passGraph E out vertices seen ctx ty) ⊓ scanGraph E seen ctx ty h
  have input : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have result : Nonempty (Derivation body (A :: Γ) (memberGraph out h)) := by
    apply reportCases E vertices h tail seen ctx ty out _ (Derivation.conjunctionLeft input)
    intro β j Δ rest keep row
    rw [graphRename]
    have g := renameInto ⟨Derivation.conjunctionRight input⟩ j Δ keep
    rw [scanRename] at g
    obtain ⟨g⟩ := g
    exact headRow E _ _ _ _ _ _ g (Derivation.conjunctionRight row)
  obtain ⟨r⟩ := result
  exact ⟨Derivation.implicationIntroduction r⟩

private theorem tailRow (E : Program 4) (h tail seen ctx ty out supplied actual k : OTerm α)
    (run : Derivation body Γ (passGraph E supplied tail seen ctx ty))
    (member : Derivation body Γ (memberGraph supplied k))
    (row : Derivation body Γ (restRow E out h tail actual seen ctx ty)) :
    Nonempty (Derivation body Γ (memberGraph out k)) := by
  obtain ⟨same⟩ := valueUnique (pass E) supplied actual (passTape tail seen ctx ty) ⟨run⟩ ⟨Derivation.conjunctionLeft row⟩
  have aligned : Nonempty (Derivation body Γ (memberGraph actual k)) :=
    headTransport scratchMember (suc z) supplied actual ![k] ⟨same⟩ ⟨member⟩
  obtain ⟨aligned⟩ := aligned
  let L := scanGraph E seen ctx ty h ⊓ cell out h actual
  let R := (scanGraph E seen ctx ty h).not ⊓ eqn out actual
  have l : Derivation body (L :: Γ) L := Derivation.hypothesis List.mem_cons_self
  obtain ⟨left⟩ := tailMember out h actual k ⟨Derivation.conjunctionRight l⟩ ⟨addHyp aligned L⟩
  have r : Derivation body (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
  have right : Nonempty (Derivation body (R :: Γ) (memberGraph out k)) :=
    headTransport scratchMember (suc z) actual out ![k] ⟨symm (Derivation.conjunctionRight r)⟩ ⟨addHyp aligned R⟩
  obtain ⟨right⟩ := right
  exact ⟨disjunctionElimination (Derivation.conjunctionRight row)
    (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

theorem exact_FilteredTailRetained : ExactFilteredTailRetained := by
  intro E body α Γ vertices h tail seen ctx ty out rest k
  let A := (cell vertices h tail ⊓ passGraph E out vertices seen ctx ty) ⊓
    (passGraph E rest tail seen ctx ty ⊓ memberGraph rest k)
  have input : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have actual := Derivation.conjunctionRight input
  have result : Nonempty (Derivation body (A :: Γ) (memberGraph out k)) := by
    apply reportCases E vertices h tail seen ctx ty out _ (Derivation.conjunctionLeft input)
    intro β j Δ v keep row
    rw [graphRename]
    have r := renameInto ⟨Derivation.conjunctionLeft actual⟩ j Δ keep
    rw [passRename] at r
    have m := renameInto ⟨Derivation.conjunctionRight actual⟩ j Δ keep
    rw [graphRename] at m
    obtain ⟨r⟩ := r
    obtain ⟨m⟩ := m
    exact tailRow E _ _ _ _ _ _ _ _ _ r m row
  obtain ⟨r⟩ := result
  exact ⟨Derivation.implicationIntroduction r⟩

#print axioms exact_ScannedHeadRetained
#print axioms exact_FilteredTailRetained
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterRetentionChecks
