module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalFiniteBlocks
open InternalModularArithmetic InternalFiniteBlocksBindingProof InternalFiniteBlocksProof
open InternalGraphCompositionSyntaxProof InternalTagArithmeticSyntaxProof
open InternalSourceInversionSupportProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalBinderTransportSyntaxProof InternalBetaWitnessProof
open InternalAdditionCancellationProof InternalQuotientGapProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalBetaDivisionSyntaxProof
open InternalBinderTransportProof
open InternalDerivationRenamingArithmeticProof InternalDerivationRenamingSyntaxProof

abbrev cf {α : Type} (a b m : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (congruent a b m)

theorem equationEmbedding {α : Type} (a b m q p : OrdinaryArithmetic.Term α) :
    arithmeticEmbedding.onFormula (equation a b m q p) = eqn (add a (mul q m)) (add b (mul p m)) :=
  onEquality arithmeticEmbedding _ _

theorem actualMatrix : InternalModularArithmeticTargets.ActualMatrix := by
  intro α a b m
  exact actualOriginalBlockEmbedding α 2 (matrix a b m)

theorem matrixSubst {α : Type} (a b m : OrdinaryArithmetic.Term α) (ts : Fin 2 → OrdinaryArithmetic.Term α) :
    (arithmeticEmbedding.onFormula (matrix a b m)).subst (Sum.elim Term.var (fun j => emb (ts j))) =
    arithmeticEmbedding.onFormula (equation a b m (ts 0) (ts 1)) := by
  have he : (Sum.elim Term.var (fun j => emb (ts j))) =
      (fun x => emb (Sum.elim Term.var ts x)) := by
    funext x
    cases x <;> rfl
  rw [he,← embedSubst]
  have ht (t : OrdinaryArithmetic.Term α) : (t.relabel Sum.inl).subst (Sum.elim Term.var ts) = t := by
    rw [termRelabelSubst]
    exact termSubstVar t
  unfold matrix equation
  congr 1
  simp only [equalitySubstitution,addSubst,mulSubst,ht,Term.subst,Sum.elim_inr]

theorem actualIntroduction : InternalModularArithmeticTargets.ActualIntroduction := by
  intro body α Gamma a b m q p h
  rw [actualMatrix]
  apply actualFiniteExistentialIntroduction body α 2 Gamma _ (fun j => emb (Fin.cases q (fun _ => p) j))
  rw [matrixSubst]
  exact h

theorem actualElimination : InternalModularArithmeticTargets.ActualElimination := by
  intro body α Gamma a b m psi h e
  rw [actualMatrix] at h
  exact actualFiniteExistentialElimination body α 2 Gamma _ psi h e

theorem actualReflexivity : InternalModularArithmeticTargets.ActualReflexivity := by
  intro body α a m
  apply actualIntroduction body α [] a a m z z
  rw [equationEmbedding]
  exact ⟨Derivation.equalityReflexivity _⟩

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Combine witness offsets without interpreting any term in the natural numbers. -/
def offsetSum (a q r m : OrdinaryArithmetic.Term α) :
    Derivation body Gamma (eqn (add a (mul (add q r) m)) (add (add a (mul q m)) (mul r m))) :=
  trans (congAddLeft a (leftDistributivity q r m)) (symm (associativity a (mul q m) (mul r m)))

def fourSum (a b c d : OrdinaryArithmetic.Term α) :
    Derivation body Gamma (eqn (add (add a b) (add c d)) (add (add a c) (add b d))) :=
  trans (symm (associativity (add a b) c d))
    (trans (InternalMultiplicationLawsProof.congAddRight d (swapMiddle a b c)) (associativity (add a c) b d))

theorem actualWitnessSymmetry : InternalModularArithmeticTargets.ActualWitnessSymmetry := by
  intro body α Gamma a b m q p h
  rw [equationEmbedding] at h ⊢
  obtain ⟨h⟩ := h
  exact ⟨symm h⟩

theorem actualWitnessTransitivity : InternalModularArithmeticTargets.ActualWitnessTransitivity := by
  intro body α Gamma a b c m q p r s h k
  rw [equationEmbedding] at h k ⊢
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨trans (offsetSum a q r m)
    (trans (InternalMultiplicationLawsProof.congAddRight (mul r m) h)
      (trans (swapMiddle b (mul p m) (mul r m))
        (trans (InternalMultiplicationLawsProof.congAddRight (mul p m) k) (symm (offsetSum c s p m)))))⟩

theorem actualWitnessAddition : InternalModularArithmeticTargets.ActualWitnessAddition := by
  intro body α Gamma a b c d m q p r s h k
  rw [equationEmbedding] at h k ⊢
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨trans (congAddLeft (add a c) (leftDistributivity q r m))
    (trans (fourSum a c (mul q m) (mul r m))
      (trans (InternalMultiplicationLawsProof.congAddRight (add c (mul r m)) h)
        (trans (congAddLeft (add b (mul p m)) k)
          (trans (fourSum b (mul p m) d (mul s m))
            (symm (congAddLeft (add b d) (leftDistributivity p s m)))))))⟩

def scaleOffset (a q m c : OrdinaryArithmetic.Term α) :
    Derivation body Gamma (eqn (mul c (add a (mul q m)))
      (add (mul c a) (mul (mul c q) m))) :=
  trans (distributivity c a (mul q m))
    (congAddLeft (mul c a) (symm (multiplicationAssociativity c q m)))

theorem actualWitnessMultiplication : InternalModularArithmeticTargets.ActualWitnessMultiplication := by
  intro body α Gamma a b m q p c h
  rw [equationEmbedding] at h ⊢
  obtain ⟨h⟩ := h
  exact ⟨trans (symm (scaleOffset a q m c)) (trans (congMulLeft c h) (scaleOffset b p m c))⟩

/-- Rename free variables through the literal existing bounded existential block. -/
theorem congruentRename {α β : Type} (a b m : OrdinaryArithmetic.Term α) (j : α → β) :
    (cf a b m).relabel j = cf (a.relabel j) (b.relabel j) (m.relabel j) := by
  unfold cf
  rw [← arithmeticRename,formulaRelabel]
  unfold congruent OrdinaryArithmetic.existsFin matrix equation
  rw [exsRename,bindEquality,bindEquality]
  congr 1
  simp only [rename,BoundedFormula.mapTermRel,Term.bdEqual,
    OrdinaryArithmetic.addTerm,OrdinaryArithmetic.mulTerm,binaryRelabel,
    Term.relabel_relabel,Term.relabel]
  rfl

theorem equationRename {α β : Type} (a b m q p : OrdinaryArithmetic.Term α) (j : α → β) :
    (arithmeticEmbedding.onFormula (equation a b m q p)).relabel j =
      arithmeticEmbedding.onFormula (equation (a.relabel j) (b.relabel j) (m.relabel j) (q.relabel j) (p.relabel j)) := by
  simp only [equationEmbedding,eqnRelabel,addRelabel,mulRelabel]

theorem congruenceCases (Gamma : List (Formula α)) (a b m : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (cf a b m)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (q p : OrdinaryArithmetic.Term β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (arithmeticEmbedding.onFormula
        (equation (a.relabel j) (b.relabel j) (m.relabel j) q p))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply actualElimination body α Gamma a b m psi h
  apply k (α ⊕ Fin 2) Sum.inl _ (.var (.inr 0)) (.var (.inr 1))
  · intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualSymmetry : InternalModularArithmeticTargets.ActualSymmetry := by
  intro body α Gamma a b m h
  apply congruenceCases Gamma a b m _ h
  intro β j Delta q p _ e
  rw [congruentRename]
  exact actualIntroduction body β Delta _ _ _ p q (actualWitnessSymmetry body β Delta _ _ _ q p e)

theorem actualTransitivity : InternalModularArithmeticTargets.ActualTransitivity := by
  intro body α Gamma a b c m h k
  apply congruenceCases Gamma a b m _ h
  intro β j Delta q p hi e
  rw [congruentRename]
  have k' := renameInto k j Delta hi
  rw [congruentRename] at k'
  apply congruenceCases Delta (b.relabel j) (c.relabel j) (m.relabel j) _ k'
  intro γ l Theta r s ht f
  rw [congruentRename]
  have e' := renameInto e l Theta ht
  rw [equationRename] at e'
  exact actualIntroduction body γ Theta _ _ _ (add (q.relabel l) r) (add s (p.relabel l))
    (actualWitnessTransitivity body γ Theta _ _ _ _ _ _ _ _ e' f)

theorem actualAddition : InternalModularArithmeticTargets.ActualAddition := by
  intro body α Gamma a b c d m h k
  apply congruenceCases Gamma a b m _ h
  intro β j Delta q p hi e
  rw [congruentRename,addRelabel,addRelabel]
  have k' := renameInto k j Delta hi
  rw [congruentRename] at k'
  apply congruenceCases Delta (c.relabel j) (d.relabel j) (m.relabel j) _ k'
  intro γ l Theta r s ht f
  rw [congruentRename,addRelabel,addRelabel]
  have e' := renameInto e l Theta ht
  rw [equationRename] at e'
  exact actualIntroduction body γ Theta _ _ _ (add (q.relabel l) r) (add (p.relabel l) s)
    (actualWitnessAddition body γ Theta _ _ _ _ _ _ _ _ _ e' f)

theorem actualMultiplication : InternalModularArithmeticTargets.ActualMultiplication := by
  intro body α Gamma a b m c h
  apply congruenceCases Gamma a b m _ h
  intro β j Delta q p _ e
  rw [congruentRename,mulRelabel,mulRelabel]
  exact actualIntroduction body β Delta _ _ _ (mul (c.relabel j) q) (mul (c.relabel j) p)
    (actualWitnessMultiplication body β Delta _ _ _ _ _ _ e)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticProof
