module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBinaryCRT
open InternalModularArithmeticProof
open InternalFiniteBlocksBindingProof InternalFiniteBlocksProof InternalGraphCompositionSyntaxProof
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalDerivationRenamingArithmeticProof InternalDerivationRenamingSyntaxProof
open SourceComputabilityFormulaSupportProof InternalOriginalOrderSyntaxProof
open InternalBetaDivisionSyntaxProof InternalBetaWitnessProof

theorem congruentSubst {α β : Type} (a b m : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (cf a b m).subst (fun x => emb (ts x)) = cf (a.subst ts) (b.subst ts) (m.subst ts) := by
  unfold cf
  rw [← embedSubst]
  have ht (u : OrdinaryArithmetic.Term α) :
      (u.relabel (Sum.inl : α → α ⊕ Fin 2)).subst
        (Sum.elim (fun x => (ts x).relabel Sum.inl) (fun i => .var (.inr i))) =
      (u.subst ts).relabel Sum.inl := by
    rw [termRelabelSubst,termSubstRelabel]; rfl
  unfold InternalModularArithmetic.congruent InternalModularArithmetic.matrix InternalModularArithmetic.equation
  rw [existsFinSubst,equalitySubstitution]
  congr 1
  simp only [addSubst,mulSubst,ht,Term.subst,Sum.elim_inr]

theorem congruentInstantiate {α : Type} (a b m : OrdinaryArithmetic.Term (α ⊕ Fin 1))
    (u : OrdinaryArithmetic.Term α) :
    instantiate (cf a b m) (emb u) =
      cf (a.subst (bindTerm u)) (b.subst (bindTerm u)) (m.subst (bindTerm u)) := by
  rw [instantiate,bindEmbedding,congruentSubst]

theorem solutionRename {α β : Type} (a b r s : OrdinaryArithmetic.Term α) (j : α → β) :
    (solution a b r s).relabel j =
      solution (a.relabel j) (b.relabel j) (r.relabel j) (s.relabel j) := by
  unfold solution
  rw [existsRename]
  change existsOne (((cf (.var (.inr 0)) (r.relabel Sum.inl) (a.relabel Sum.inl)).relabel (Sum.map j id)) ⊓
    ((cf (.var (.inr 0)) (s.relabel Sum.inl) (b.relabel Sum.inl)).relabel (Sum.map j id))) = _
  simp only [congruentRename,Term.relabel_relabel,Term.relabel]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
def solutionIntroduction (a b r s c : OrdinaryArithmetic.Term α)
    (h : Derivation body Gamma (cf c r a ⊓ cf c s b)) :
    Derivation body Gamma (solution a b r s) := by
  apply Derivation.existentialIntroduction (emb c)
  change Derivation body Gamma
    (instantiate (cf (.var (.inr 0)) (r.relabel Sum.inl) (a.relabel Sum.inl)) (emb c) ⊓
     instantiate (cf (.var (.inr 0)) (s.relabel Sum.inl) (b.relabel Sum.inl)) (emb c))
  simpa only [congruentInstantiate,liftBind,varBind] using h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTSyntaxProof
