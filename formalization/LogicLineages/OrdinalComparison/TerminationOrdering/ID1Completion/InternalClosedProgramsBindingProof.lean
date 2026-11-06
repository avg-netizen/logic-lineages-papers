module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalFiniteBlocks InternalClosedPrograms
open SourceComputabilityFormulaSupportProof InternalBinderTransportSyntaxProof
open InternalFiniteBlocksBindingProof InternalFiniteBlocksSubstitutionProof
open InternalTermSubstitutionProof InternalDerivationRenamingProof

theorem allBlockZero {α : Type} (phi : Formula (α ⊕ Fin 0)) :
    allBlock phi = phi.relabel eraseZero := blockZero phi

theorem allBlockLast {α : Type} (k : Nat) (phi : Formula (α ⊕ Fin (k+1))) :
    allBlock phi = allBlock (allOne (phi.relabel (splitLast k))) := by
  have h := rebind phi (splitLast k) (id : α ⊕ Fin k → α ⊕ Fin k)
  rw [combineLast,BoundedFormula.castLE_rfl] at h
  change (BoundedFormula.relabel id phi).all.alls =
    (BoundedFormula.relabel id ((BoundedFormula.relabel id (phi.relabel (splitLast k))).all)).alls
  rw [BoundedFormula.relabel_all,formulaRelabel,bindRename]
  change (BoundedFormula.relabel id phi).all.alls =
    ((BoundedFormula.relabel id (BoundedFormula.relabel (splitLast k) phi)).all).alls
  rw [h]

theorem actualUniversalBinderEquations : InternalClosedProgramsTargets.ActualUniversalBinderEquations := by
  exact ⟨fun _ => allBlockZero,fun _ => allBlockLast⟩

theorem onAlls {L L' : Language} (h : L →ᴸ L') {α : Type} {k : Nat}
    (phi : L.BoundedFormula α k) :
    h.onFormula phi.alls = (h.onBoundedFormula phi).alls := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change h.onFormula phi.all.alls = _
    rw [ih]
    rfl

theorem actualOriginalUniversalEmbedding : InternalClosedProgramsTargets.ActualOriginalUniversalEmbedding := by
  intro α k phi
  change arithmeticEmbedding.onFormula (BoundedFormula.relabel id phi).alls = _
  rw [onAlls,onBind]
  rfl

theorem introduction (body : Positive (Fin 1)) (α : Type) (k : Nat) :
    ∀ (Gamma : List (Formula α)) (phi : Formula (α ⊕ Fin k)),
    Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl)) phi) →
    Nonempty (Derivation body Gamma (allBlock phi)) := by
  induction k with
  | zero =>
    intro Gamma phi ⟨d⟩
    obtain ⟨e⟩ := renameDerivation d α eraseZero
    simp only [contextZero] at e
    rw [allBlockZero]
    exact ⟨e⟩
  | succ k ih =>
    intro Gamma phi ⟨d⟩
    obtain ⟨e⟩ := renameDerivation d ((α ⊕ Fin k) ⊕ Fin 1) (splitLast k)
    simp only [contextLast] at e
    rw [allBlockLast]
    apply ih Gamma (allOne (phi.relabel (splitLast k)))
    exact ⟨Derivation.universalIntroduction e⟩

theorem actualFiniteUniversalIntroduction : InternalClosedProgramsTargets.ActualFiniteUniversalIntroduction := by
  intro body α k
  exact introduction body α k

theorem elimination (body : Positive (Fin 1)) (α : Type) (k : Nat) :
    ∀ (Gamma : List (Formula α)) (phi : Formula (α ⊕ Fin k)) (ts : Fin k → Term α),
    Nonempty (Derivation body Gamma (allBlock phi)) →
    Nonempty (Derivation body Gamma (phi.subst (Sum.elim Term.var ts))) := by
  induction k with
  | zero =>
    intro Gamma phi ts h
    rw [allBlockZero] at h
    rw [zeroWitness]
    exact h
  | succ k ih =>
    intro Gamma phi ts h
    rw [allBlockLast] at h
    obtain ⟨e⟩ := ih Gamma (allOne (phi.relabel (splitLast k))) (fun i => ts i.castSucc) h
    rw [actualUniversalSubstitution] at e
    have d := Derivation.universalElimination (ts (Fin.last k)) e
    have he := witnessLast k phi ts
    unfold witnessesBeforeLast at he
    rw [he] at d
    exact ⟨d⟩

theorem actualFiniteUniversalElimination : InternalClosedProgramsTargets.ActualFiniteUniversalElimination := by
  intro body α k
  exact elimination body α k
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
