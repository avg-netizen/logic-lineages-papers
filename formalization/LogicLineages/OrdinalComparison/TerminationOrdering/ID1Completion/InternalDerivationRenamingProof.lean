module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof InternalDerivationRenamingArithmeticProof

/-- Structural recursion on the existing proof datatype, not a new constructor. -/
theorem renameDerivation {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    {phi : Formula α} (d : Derivation body Gamma phi) :
    ∀ (β : Type) (f : α → β),
    Nonempty (Derivation body (Gamma.map (fun p => p.relabel f)) (phi.relabel f)) := by
  induction d with
  | hypothesis h =>
    intro β f
    exact ⟨Derivation.hypothesis (List.mem_map_of_mem h)⟩
  | weakening h d ih =>
    intro β f
    obtain ⟨e⟩ := ih β f
    apply Nonempty.intro
    apply Derivation.weakening ?_ e
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact List.mem_map.mpr ⟨q,h q hq,rfl⟩
  | implicationIntroduction d ih =>
    intro β f
    obtain ⟨e⟩ := ih β f
    exact ⟨Derivation.implicationIntroduction e⟩
  | implicationElimination d e ihd ihe =>
    intro β f
    obtain ⟨d'⟩ := ihd β f
    obtain ⟨e'⟩ := ihe β f
    exact ⟨Derivation.implicationElimination d' e'⟩
  | conjunctionIntroduction d e ihd ihe =>
    intro β f
    obtain ⟨d'⟩ := ihd β f
    obtain ⟨e'⟩ := ihe β f
    exact ⟨Derivation.conjunctionIntroduction d' e'⟩
  | conjunctionLeft d ih =>
    intro β f
    obtain ⟨e⟩ := ih β f
    exact ⟨Derivation.conjunctionLeft e⟩
  | conjunctionRight d ih =>
    intro β f
    obtain ⟨e⟩ := ih β f
    exact ⟨Derivation.conjunctionRight e⟩
  | explosion d ih =>
    intro β f
    obtain ⟨e⟩ := ih β f
    exact ⟨Derivation.explosion e⟩
  | classical d ih =>
    intro β f
    obtain ⟨e⟩ := ih β f
    exact ⟨Derivation.classical e⟩
  | @universalIntroduction α Gamma phi d ih =>
    intro β f
    obtain ⟨e⟩ := ih (β ⊕ Fin 1) (Sum.map f id)
    rw [contextWeakenRename] at e
    rw [actualUniversalRenaming]
    exact ⟨Derivation.universalIntroduction e⟩
  | @universalElimination α Gamma phi t d ih =>
    intro β f
    obtain ⟨e⟩ := ih β f
    rw [actualUniversalRenaming] at e
    rw [instantiateRename]
    exact ⟨Derivation.universalElimination (t.relabel f) e⟩
  | @existentialIntroduction α Gamma phi t d ih =>
    intro β f
    obtain ⟨e⟩ := ih β f
    rw [instantiateRename] at e
    rw [existsRename]
    exact ⟨Derivation.existentialIntroduction (t.relabel f) e⟩
  | @existentialElimination α Gamma phi psi d e ihd ihe =>
    intro β f
    obtain ⟨d'⟩ := ihd β f
    obtain ⟨e'⟩ := ihe (β ⊕ Fin 1) (Sum.map f id)
    rw [existsRename] at d'
    simp only [List.map_cons,contextWeakenRename,weakenRename] at e'
    exact ⟨Derivation.existentialElimination d' e'⟩
  | equalityReflexivity t =>
    intro β f
    rw [equalityRename]
    exact ⟨Derivation.equalityReflexivity (t.relabel f)⟩
  | @equalityElimination α Gamma theta t u d e ihd ihe =>
    intro β f
    obtain ⟨d'⟩ := ihd β f
    obtain ⟨e'⟩ := ihe β f
    rw [equalityRename] at d'
    rw [instantiateRename] at e'
    rw [instantiateRename]
    exact ⟨Derivation.equalityElimination (theta.relabel (Sum.map f id))
      (t.relabel f) (u.relabel f) d' e'⟩
  | arithmetic w =>
    intro β f
    rw [arithmeticRenameFormula]
    exact ⟨Derivation.arithmetic (renameArithmetic f w)⟩
  | @inductiveClosure α Gamma =>
    intro β f
    rw [closureRename]
    exact ⟨Derivation.inductiveClosure⟩
  | @inductiveLeastness α Gamma theta =>
    intro β f
    rw [leastnessRename]
    exact ⟨Derivation.inductiveLeastness (theta.relabel (Sum.map f id))⟩

theorem actualDerivationRenaming : InternalDerivationRenamingTargets.ActualDerivationRenaming := by
  intro body α β f Gamma phi ⟨d⟩
  exact renameDerivation d β f

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingProof
