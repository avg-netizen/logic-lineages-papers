module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaSemanticsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof PositiveArithmeticOperatorsSupportProof
open PositiveArithmeticTransformsProof PositiveArithmeticSchemasProof
open PositiveArithmeticPredicateSubstitution PositiveArithmeticPredicateSubstitutionProof
open TaggedArithmeticOperatorsSupportProof InternalCalculus JointGammaInvariant

theorem branchTruth {α : Type} (odd : Bool) (phi : Formula (α ⊕ Fin 1))
    (P : Nat → Prop) (v : α → Nat) (z : Nat) :
    realize P (branch odd phi) (Sum.elim v (fun _ => z)) ↔
      ∀ x, z = tagNumber odd x → realize P phi (Sum.elim v (fun _ => x)) := by
  rw [branch,allScalarTruth]
  apply forall_congr'
  intro x
  rw [generalImpTruth,embeddingTruth,FirstOrder.Language.Formula.realize_equal,tagTermTruth]
  change (z = tagNumber odd x →
    realize P (liftPredicateFormula phi) (Sum.elim (Sum.elim v (fun _ => z)) (fun _ => x))) ↔ _
  exact imp_congr Iff.rfl (actualLiftPredicateFormulaTruth α phi P v (fun _ => z) x)

theorem sameBranch {α : Type} (odd : Bool) (phi : Formula (α ⊕ Fin 1))
    (P : Nat → Prop) (v : α → Nat) (x : Nat) :
    realize P (branch odd phi) (Sum.elim v (fun _ => tagNumber odd x)) ↔
      realize P phi (Sum.elim v (fun _ => x)) := by
  rw [branchTruth]
  constructor
  · intro h
    exact h x rfl
  · intro h y he
    have hy := tagInjective odd he
    subst y
    exact h

theorem actualTaggedInvariantBranches : JointGammaInvariantTargets.ActualTaggedInvariantBranches := by
  intro α scalar multiset P v x
  constructor
  · rw [tagged,generalConjTruth,sameBranch,branchTruth]
    exact ⟨And.left,fun h => ⟨h,fun y he => False.elim (tagsDisjoint x y he)⟩⟩
  · rw [tagged,generalConjTruth,branchTruth,sameBranch]
    exact ⟨And.right,fun h => ⟨fun y he => False.elim (tagsDisjoint y x he.symm),h⟩⟩

theorem replacementTruth {α : Type} (body : Positive (Fin 1))
    (theta : Formula (α ⊕ Fin 1)) (P : Nat → Prop) (v : α → Nat) (x : Nat) :
    realize P (replacedBody body theta) (Sum.elim v (fun _ => x)) ↔
      realize (fun y => realize P theta (Sum.elim v (fun _ => y))) body.formula ![x] := by
  rw [replacedBody,PositiveArithmeticSchemasProof.replacementTruth,
    InternalCalculusSupportProof.parameterBodyTruth]
  have hv : (fun _ : Fin 1 => x) = ![x] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [hv]

theorem actualOriginalReplacementBranches : JointGammaInvariantTargets.ActualOriginalReplacementBranches := by
  intro data n arity hcal context α scalar multiset P v x
  have hsource := JointGammaSemanticsProof.actualClosedSourceOperator data n arity hcal context
    (fun y => realize P (tagged scalar multiset) (Sum.elim v (fun _ => y))) x
  constructor
  · rw [replacementTruth]
    exact hsource.1.trans (and_congr Iff.rfl (forall_congr' (fun y =>
      imp_congr Iff.rfl (actualTaggedInvariantBranches α scalar multiset P v y).1)))
  · rw [replacementTruth]
    exact hsource.2.trans (and_congr Iff.rfl (forall_congr' (fun y =>
      imp_congr Iff.rfl (actualTaggedInvariantBranches α scalar multiset P v y).2)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantSupportProof
