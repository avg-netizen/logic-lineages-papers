module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalitySyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalCoprimeMultipleSyntaxProof InternalRelationalCRTSyntaxProof
open InternalBinderTransportSyntaxProof InternalTermSubstitutionSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalLeastNumberSyntaxProof InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalBetaDivisionSyntaxProof InternalBetaTotalitySyntaxProof InternalBetaCoding

theorem codedBelowRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (a b n : OTerm α) (j : α → β) :
    (codedBelow R a b n).relabel j = codedBelow (R.relabel (Sum.map (Sum.map j id) id))
      (a.relabel j) (b.relabel j) (n.relabel j) := by
  unfold codedBelow
  rw [boundedRename,existsRename]
  change InternalCoprimeMultiple.bounded (existsOne (R.relabel _ ⊓
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula _ _ _ _)).relabel _)) _ = _
  rw [betaRename]
  simp only [Term.relabel_relabel,mapInl,Term.relabel,Sum.map_inl,Sum.map_inr,id_eq]
  rfl

theorem codedBelowSubst {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (a b n : OTerm α) (ts : α → OTerm β) :
    (codedBelow R a b n).subst (fun x => emb (ts x)) =
    codedBelow (R.subst (fun x => emb (liftTerms (liftTerms ts) x)))
      (a.subst ts) (b.subst ts) (n.subst ts) := by
  unfold codedBelow
  rw [boundedSubst,existsSubst,liftEmbedding,infSubst,betaSubst]
  simp only [liftSubst]
  rfl

theorem codeWithRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (a n : OTerm α) (j : α → β) :
    (codeWith R a n).relabel j = codeWith (R.relabel (Sum.map (Sum.map j id) id))
      (a.relabel j) (n.relabel j) := by
  rw [codeWith,existsRename,codedBelowRename,relationLiftRename]
  simp only [codeWith,Term.relabel_relabel,mapInl,varMap]

theorem codeWithSubst {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (a n : OTerm α) (ts : α → OTerm β) :
    (codeWith R a n).subst (fun x => emb (ts x)) =
    codeWith (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) (a.subst ts) (n.subst ts) := by
  rw [codeWith,existsSubst,liftEmbedding,codedBelowSubst,relationLiftSubst]
  simp only [liftSubst]
  rfl

theorem codingRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n : OTerm α) (j : α → β) :
    (coding R n).relabel j = coding (R.relabel (Sum.map (Sum.map j id) id)) (n.relabel j) := by
  rw [coding,existsRename,codeWithRename,relationLiftRename]
  simp only [coding,Term.relabel_relabel,mapInl,varMap]

theorem codingSubst {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n : OTerm α) (ts : α → OTerm β) :
    (coding R n).subst (fun x => emb (ts x)) =
    coding (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) (n.subst ts) := by
  rw [coding,existsSubst,liftEmbedding,codeWithSubst,relationLiftSubst]
  simp only [liftSubst]
  rfl

theorem codeWithMatrixInstantiate {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (a b n : OTerm α) :
    instantiate (codedBelow (R.relabel (Sum.map (Sum.map Sum.inl id) id))
      (a.relabel Sum.inl) (.var (.inr 0)) (n.relabel Sum.inl)) (emb b) = codedBelow R a b n := by
  rw [instantiate,bindEmbedding,codedBelowSubst,relationLiftBind,liftBind,varBind,liftBind]

theorem codingMatrixInstantiate {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (a n : OTerm α) :
    instantiate (codeWith (R.relabel (Sum.map (Sum.map Sum.inl id) id))
      (.var (.inr 0)) (n.relabel Sum.inl)) (emb a) = codeWith R a n := by
  rw [instantiate,bindEmbedding,codeWithSubst,relationLiftBind,varBind,liftBind]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem codeWithIntroduction (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (a b n : OTerm α)
    (h : Nonempty (Derivation body Gamma (codedBelow R a b n))) :
    Nonempty (Derivation body Gamma (codeWith R a n)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb b)
  rw [codeWithMatrixInstantiate]
  exact h

theorem codingIntroduction (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (a b n : OTerm α)
    (h : Nonempty (Derivation body Gamma (codedBelow R a b n))) :
    Nonempty (Derivation body Gamma (coding R n)) := by
  obtain ⟨h⟩ := codeWithIntroduction R a b n h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb a)
  rw [codingMatrixInstantiate]
  exact h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingSyntaxProof
