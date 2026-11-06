module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalOrientedBezout
open InternalFiniteBlocksBindingProof InternalFiniteBlocksProof InternalGraphCompositionSyntaxProof
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalDerivationRenamingArithmeticProof InternalDerivationRenamingSyntaxProof
open SourceComputabilityFormulaSupportProof InternalOriginalOrderSyntaxProof
open InternalBetaDivisionSyntaxProof InternalBetaWitnessProof
abbrev of {α : Type} (a b : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (oriented a b)

theorem matrixSubst {α : Type} (a b : OrdinaryArithmetic.Term α) (ts : Fin 2 → OrdinaryArithmetic.Term α) :
    (arithmeticEmbedding.onFormula (matrix a b)).subst (Sum.elim Term.var (fun j => emb (ts j))) =
    arithmeticEmbedding.onFormula (InternalBezoutCRT.certificate (suc a) b (ts 0) (ts 1)) := by
  have he : (Sum.elim Term.var (fun j => emb (ts j))) = (fun x => emb (Sum.elim Term.var ts x)) := by
    funext x; cases x <;> rfl
  rw [he,← embedSubst]
  have ht (t : OrdinaryArithmetic.Term α) : (t.relabel Sum.inl).subst (Sum.elim Term.var ts) = t := by
    rw [termRelabelSubst]; exact termSubstVar t
  unfold matrix InternalBezoutCRT.certificate
  congr 1
  simp only [equalitySubstitution,sucSubst,mulSubst,ht,Term.subst,Sum.elim_inr]

theorem orientedRename {α β : Type} (a b : OrdinaryArithmetic.Term α) (j : α → β) :
    (of a b).relabel j = of (a.relabel j) (b.relabel j) := by
  unfold of
  rw [← arithmeticRename,formulaRelabel]
  unfold oriented OrdinaryArithmetic.existsFin matrix InternalBezoutCRT.certificate
  rw [exsRename,bindEquality,bindEquality]
  congr 1
  simp only [rename,BoundedFormula.mapTermRel,Term.bdEqual,
    sucRelabel,mulRelabel,
    Term.relabel_relabel,Term.relabel]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem orientedIntroduction (a b u v : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma
      (arithmeticEmbedding.onFormula (InternalBezoutCRT.certificate (suc a) b u v)))) :
    Nonempty (Derivation body Gamma (of a b)) := by
  rw [of,oriented,actualOriginalBlockEmbedding]
  apply actualFiniteExistentialIntroduction body α 2 Gamma _ (fun j => emb (![u,v] j))
  rw [matrixSubst]
  exact h

theorem orientedCases (Gamma : List (Formula α)) (a b : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (of a b)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (u v : OrdinaryArithmetic.Term β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (arithmeticEmbedding.onFormula
        (InternalBezoutCRT.certificate (suc (a.relabel j)) (b.relabel j) u v))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  rw [of,oriented,actualOriginalBlockEmbedding] at h
  apply actualFiniteExistentialElimination body α 2 Gamma _ psi h
  apply k (α ⊕ Fin 2) Sum.inl _ (.var (.inr 0)) (.var (.inr 1))
  · intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  · have h : Derivation body (arithmeticEmbedding.onFormula (matrix a b) :: Gamma.map (fun p => p.relabel Sum.inl)) (arithmeticEmbedding.onFormula (matrix a b)) :=
      Derivation.hypothesis List.mem_cons_self
    simpa only [matrix,sucRelabel] using (show Nonempty (Derivation body _ _) from ⟨h⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutSyntaxProof
