module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundProof
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof SourceComputabilityFormulaProof NumberedLeastCodeRepresentative
open InternalCalculus SourceEndpoint GuardedSource GuardedSourceGround
open InternalSourceInversionSupportProof InternalPositiveUnfoldingSupportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof

/-- The literal successor body of the existing scalar accessibility operator. -/
def successorBody (edge : OrdinaryArithmetic.Formula (Fin 3)) : Positive (Fin 2 ⊕ Fin 1) :=
  .guarded (edge.subst ![.var (.inl 0),.var (.inl 1),.var (.inr (0 : Fin 1))])
    (.predicate (tagTerm false (.var (.inr (0 : Fin 1)))))

theorem successorInstance {α : Type} (edge : OrdinaryArithmetic.Formula (Fin 3))
    (context x y : OrdinaryArithmetic.Term α) :
    instantiate (substitutePositive
      (Sum.elim (fun a => (![context,x] a).relabel Sum.inl) (fun i : Fin 1 => .var (.inr i)))
      (successorBody edge)).formula (arithmeticEmbedding.onTerm y) =
    (arithmeticEmbedding.onFormula (edge.subst ![context,x,y])).imp (literalGround y) := by
  rw [positiveInstantiation]
  change (arithmeticEmbedding.onFormula
    ((edge.subst ![.var (.inl 0),.var (.inl 1),.var (.inr (0 : Fin 1))]).subst
      (Sum.elim ![context,x] (fun _ : Fin 1 => y)))).imp
    (Positive.predicate ((tagTerm false (.var (.inr (0 : Fin 1)))).subst
      (Sum.elim ![context,x] (fun _ : Fin 1 => y)))).formula = _
  rw [formulaSubstComposition,tagSubstitution]
  have hs : (fun i : Fin 3 =>
      (![(.var (.inl 0) : OrdinaryArithmetic.Term (Fin 2 ⊕ Fin 1)),
        .var (.inl 1),.var (.inr 0)] i).subst
          (Sum.elim ![context,x] (fun _ : Fin 1 => y))) = ![context,x,y] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl
      (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
  rw [hs]
  rfl

theorem scalarDownward : GuardedSourceGroundTargets.ActualScalarDownward := by
  intro source context α x y
  obtain ⟨inversion⟩ := InternalSourceInversionProof.actualInternalScalarInversion source context α x
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  have h : Derivation (SourcePresentation.sourceBody source context)
      [literalGround x ⊓ literalR source context x y]
      (literalGround x ⊓ literalR source context x y) :=
    Derivation.hypothesis List.mem_cons_self
  have hi := Derivation.implicationElimination (weakenClosed inversion _)
    (Derivation.conjunctionLeft h)
  have hs := Derivation.conjunctionRight hi
  change Derivation _ _ (allOne (substitutePositive
    (Sum.elim (fun a : Fin 2 => (![numeral context,x] a).relabel Sum.inl)
      (fun i : Fin 1 => .var (.inr i)))
    (successorBody (OrdinaryArithmeticQuotient.certificateGraph source.positive))).formula) at hs
  have step := Derivation.universalElimination (arithmeticEmbedding.onTerm y) hs
  rw [successorInstance] at step
  exact Derivation.implicationElimination step (Derivation.conjunctionRight h)

theorem groundFormula : GuardedSourceGroundTargets.ActualGroundFormula := by
  intro comp context α x
  let ts : Fin 2 → OrdinaryArithmetic.Term α := ![numeral context,x]
  have ht : (typedAt (JointGammaTyped.typedFormula comp.typed) .ground).subst
      (fun i => arithmeticEmbedding.onTerm (ts i)) =
      literalTyped comp context (numeral (typeNumber .ground)) x := by
    unfold typedAt literalTyped LHom.onFormula
    rw [onFormulaSubst,formulaSubstComposition,onFormulaSubst]
    congr 1
    funext i
    refine Fin.cases rfl (fun j => Fin.cases ?_
      (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
    exact numeralSubstitution (typeNumber .ground) _
  have hp : (Positive.predicate (tagTerm false (.var (1 : Fin 2)))).formula.subst
      (fun i => arithmeticEmbedding.onTerm (ts i)) = literalGround x := by
    rw [← predicateSubstitution,tagSubstitution]
    rfl
  change ((typedAt (JointGammaTyped.typedFormula comp.typed) .ground).subst
      (fun i => arithmeticEmbedding.onTerm (ts i)) ⊓
    (Positive.predicate (tagTerm false (.var (1 : Fin 2)))).formula.subst
      (fun i => arithmeticEmbedding.onTerm (ts i))) = _
  rw [ht,hp]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundProof
