module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalLinearCombination
open InternalFiniteBlocksBindingProof InternalFiniteBlocksProof InternalGraphCompositionSyntaxProof
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalDerivationRenamingArithmeticProof InternalDerivationRenamingSyntaxProof
open SourceComputabilityFormulaSupportProof
open InternalOriginalOrderSyntaxProof InternalBetaDivisionSyntaxProof InternalBetaWitnessProof
abbrev cf {α : Type} (a b d : OrdinaryArithmetic.Term α) : Formula α := arithmeticEmbedding.onFormula (combination a b d)
theorem equationEmbedding {α : Type} (a b d x y z w : OrdinaryArithmetic.Term α) :
    arithmeticEmbedding.onFormula (equation a b d x y z w) =
    eqn (add (mul x a) (mul y b)) (add d (add (mul z a) (mul w b))) := onEquality _ _ _
theorem matrixSubst {α : Type} (a b d : OrdinaryArithmetic.Term α) (ts : Fin 4 → OrdinaryArithmetic.Term α) :
    (arithmeticEmbedding.onFormula (matrix a b d)).subst (Sum.elim Term.var (fun j => emb (ts j))) =
    arithmeticEmbedding.onFormula (equation a b d (ts 0) (ts 1) (ts 2) (ts 3)) := by
  have he : (Sum.elim Term.var (fun j => emb (ts j))) = (fun x => emb (Sum.elim Term.var ts x)) := by
    funext x; cases x <;> rfl
  rw [he,← embedSubst]
  have ht (t : OrdinaryArithmetic.Term α) : (t.relabel Sum.inl).subst (Sum.elim Term.var ts) = t := by
    rw [termRelabelSubst]; exact termSubstVar t
  unfold matrix equation
  congr 1
  simp only [equalitySubstitution,addSubst,mulSubst,ht,Term.subst,Sum.elim_inr]

theorem combinationRename {α β : Type} (a b d : OrdinaryArithmetic.Term α) (j : α → β) :
    (cf a b d).relabel j = cf (a.relabel j) (b.relabel j) (d.relabel j) := by
  unfold cf
  rw [← arithmeticRename,formulaRelabel]
  unfold combination OrdinaryArithmetic.existsFin matrix equation
  rw [exsRename,bindEquality,bindEquality]
  congr 1
  simp only [rename,BoundedFormula.mapTermRel,Term.bdEqual,
    OrdinaryArithmetic.addTerm,OrdinaryArithmetic.mulTerm,binaryRelabel,
    Term.relabel_relabel,Term.relabel]
  rfl

theorem equationRename {α β : Type} (a b d x y z w : OrdinaryArithmetic.Term α) (j : α → β) :
    (arithmeticEmbedding.onFormula (equation a b d x y z w)).relabel j =
    arithmeticEmbedding.onFormula (equation (a.relabel j) (b.relabel j) (d.relabel j)
      (x.relabel j) (y.relabel j) (z.relabel j) (w.relabel j)) := by
  simp only [equationEmbedding,eqnRelabel,addRelabel,mulRelabel]

theorem combinationSubst {α β : Type} (a b d : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (cf a b d).subst (fun x => emb (ts x)) = cf (a.subst ts) (b.subst ts) (d.subst ts) := by
  unfold cf
  rw [← embedSubst]
  have ht (u : OrdinaryArithmetic.Term α) :
      (u.relabel (Sum.inl : α → α ⊕ Fin 4)).subst
        (Sum.elim (fun x => (ts x).relabel Sum.inl) (fun i => .var (.inr i))) =
      (u.subst ts).relabel Sum.inl := by
    rw [termRelabelSubst,termSubstRelabel]; rfl
  unfold combination matrix equation
  rw [existsFinSubst,equalitySubstitution]
  congr 1
  simp only [addSubst,mulSubst,ht,Term.subst,Sum.elim_inr]

theorem combinationInstantiate {α : Type} (a b d : OrdinaryArithmetic.Term (α ⊕ Fin 1))
    (u : OrdinaryArithmetic.Term α) :
    instantiate (cf a b d) (emb u) = cf (a.subst (bindTerm u)) (b.subst (bindTerm u)) (d.subst (bindTerm u)) := by
  rw [instantiate,bindEmbedding,combinationSubst]

theorem familyInstantiate {α : Type} (a b t : OrdinaryArithmetic.Term α) :
    instantiate (arithmeticEmbedding.onFormula (positiveFamily a b)) (emb t) = cf a b (suc t) := by
  change instantiate (cf _ _ _) _ = _
  rw [combinationInstantiate]
  simp only [liftBind,sucSubst,varBind]

theorem familyRename {α β : Type} (a b : OrdinaryArithmetic.Term α) (j : α → β) :
    (arithmeticEmbedding.onFormula (positiveFamily a b)).relabel (Sum.map j id) =
    arithmeticEmbedding.onFormula (positiveFamily (a.relabel j) (b.relabel j)) := by
  change (cf _ _ _).relabel _ = cf _ _ _
  rw [combinationRename]
  simp only [sucRelabel,Term.relabel_relabel,Term.relabel]
  rfl

abbrev pf {α : Type} (a b : OrdinaryArithmetic.Term α) : Formula (α ⊕ Fin 1) :=
  arithmeticEmbedding.onFormula (positiveFamily a b)
abbrev lower {α : Type} (a b e : OrdinaryArithmetic.Term α) : Formula α :=
  InternalLeastNumberSyntaxProof.below (pf a b) e

theorem lowerRename {α β : Type} (a b e : OrdinaryArithmetic.Term α) (j : α → β) :
    (lower a b e).relabel j = lower (a.relabel j) (b.relabel j) (e.relabel j) := by
  rw [lower,InternalLeastNumberSyntaxProof.belowRename,familyRename]

theorem dividesRename {α β : Type} (d a : OrdinaryArithmetic.Term α) (j : α → β) :
    (arithmeticEmbedding.onFormula (divides d a)).relabel j =
      arithmeticEmbedding.onFormula (divides (d.relabel j) (a.relabel j)) := by
  rw [← arithmeticRename,formulaRelabel]
  unfold divides OrdinaryArithmetic.existsFin
  rw [exsRename,bindEquality,bindEquality]
  congr 1
  simp only [rename,BoundedFormula.mapTermRel,Term.bdEqual,OrdinaryArithmetic.mulTerm,
    binaryRelabel,Term.relabel_relabel,Term.relabel]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem combinationIntroduction (a b d x y z w : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation a b d x y z w)))) :
    Nonempty (Derivation body Gamma (cf a b d)) := by
  rw [cf,combination,actualOriginalBlockEmbedding]
  apply actualFiniteExistentialIntroduction body α 4 Gamma _ (fun j => emb (![x,y,z,w] j))
  rw [matrixSubst]
  exact h

theorem combinationCases (Gamma : List (Formula α)) (a b d : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (cf a b d)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (x y z w : OrdinaryArithmetic.Term β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (arithmeticEmbedding.onFormula
        (equation (a.relabel j) (b.relabel j) (d.relabel j) x y z w))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  rw [cf,combination,actualOriginalBlockEmbedding] at h
  apply actualFiniteExistentialElimination body α 4 Gamma _ psi h
  apply k (α ⊕ Fin 4) Sum.inl _ (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  · intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
theorem dividesIntroduction (d a q : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn a (mul q d)))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (divides d a))) := by
  rw [divides,actualOriginalBlockEmbedding]
  apply actualFiniteExistentialIntroduction body α 1 Gamma _ (fun _ => emb q)
  rw [onEquality]
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb q)) = (fun x => emb (bindTerm q x)) := by
    funext x; cases x <;> rfl
  rw [he]
  change Nonempty (Derivation body Gamma ((eqn (a.relabel Sum.inl) (mul (.var (.inr 0)) (d.relabel Sum.inl))).subst (fun x => emb (bindTerm q x))))
  rw [eqnSubst]
  simp only [liftBind,mulSubst,varBind]
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationSyntaxProof
