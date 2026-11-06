module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms PositiveArithmeticPredicateSubstitution
open InternalCalculus JointGammaInvariant SourceComputabilityFormulaSupportProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalSourceInversionSupportProof InternalTagArithmeticSyntaxProof
open InternalSourceIntroductionSyntaxProof

/-- Instantiation commutes with the ORIGINAL lift of an arbitrary formula. -/
theorem instantiateLift {α : Type} (phi : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (liftPredicateFormula phi) (emb (t.relabel Sum.inl)) =
      (instantiate phi (emb t)).relabel Sum.inl := by
  rw [instantiate,liftPredicateFormula,actualRelabelSubstitution,instantiate,formulaSubstRelabel]
  congr 1
  funext a
  cases a with
  | inl a => rfl
  | inr i => exact onTermRelabel arithmeticEmbedding Sum.inl t

/-- Literal original JointGammaInvariant.branch syntax after specializing its
object. The arbitrary invariant itself is left unchanged under its payload binder. -/
theorem branchInstantiate {α : Type} (odd : Bool) (phi : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (branch odd phi) (emb t) =
    allOne ((eqn (t.relabel Sum.inl) (tagTerm odd (.var (.inr (0 : Fin 1))))).imp phi) := by
  rw [instantiate,branch,onEquality]
  change (allOne ((eqn (.var (.inl (.inr (0 : Fin 1))))
    (tagTerm odd (.var (.inr (0 : Fin 1))))).imp (liftPredicateFormula phi))).subst _ = _
  rw [bindEmbedding,actualUniversalSubstitution]
  let sigma : (α ⊕ Fin 1) ⊕ Fin 1 → OTerm (α ⊕ Fin 1) :=
    Sum.elim (fun a => (bindTerm t a).relabel Sum.inl) (fun i => .var (.inr i))
  have hf : Sum.elim (fun a : α ⊕ Fin 1 => (emb (bindTerm t a)).relabel Sum.inl)
      (fun i : Fin 1 => (.var (.inr i) : Term (α ⊕ Fin 1))) = fun a => emb (sigma a) := by
    funext a
    cases a with
    | inl a => exact (onTermRelabel arithmeticEmbedding Sum.inl (bindTerm t a)).symm
    | inr i => rfl
  rw [hf]
  change allOne (((eqn (.var (.inl (.inr (0 : Fin 1))))
    (tagTerm odd (.var (.inr (0 : Fin 1))))).subst (fun a => emb (sigma a))).imp
      ((liftPredicateFormula phi).subst (fun a => emb (sigma a)))) = _
  rw [eqnSubst,tagSubstitution]
  change allOne ((eqn (t.relabel Sum.inl) (tagTerm odd (.var (.inr (0 : Fin 1))))).imp
    ((liftPredicateFormula phi).subst (fun a => emb (sigma a)))) = _
  have hp : (liftPredicateFormula phi).subst (fun a => emb (sigma a)) = phi := by
    rw [liftPredicateFormula,actualRelabelSubstitution]
    have hfun : (fun a => emb (sigma a)) ∘ Sum.map (Sum.inl : α → α ⊕ Fin 1) id = Term.var := by
      funext a
      cases a <;> rfl
    rw [hfun,formulaSubstVar]
  rw [hp]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionSyntaxProof
