module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldIndexProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldBranchesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalBinderTransportProof (actualUniversalRenaming)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalOriginalOrderSyntaxProof (notSubst)
open ID1Completion.InternalAdditionLawsProof (impInstantiate)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z eqn eqnRelabel zRelabel eqnSubst zSubst bindEmbedding varBind)
open NumberedWindowInternalSparseFieldInductionTargets NumberedWindowInternalSparseFieldExistentialProof
open NumberedWindowInternalSparseFieldIndexProof

private theorem notRename {α β : Type} (p : Formula α) (j : α → β) :
    (p.not).relabel j = (p.relabel j).not := rfl

private theorem malformedRename {α β : Type} (n : OTerm α) (j : α → β) :
    (malformed n).relabel j = malformed (n.relabel j) := by
  simp only [malformed,nonzero,equalEqn,conjunctionRename,notRename,eqnRelabel,zRelabel,someConsRename]

private theorem gapRuleRename {α β : Type} (θ : Formula (α ⊕ Fin 1)) (j : α → β) :
    (gapRule θ).relabel j = gapRule (θ.relabel (Sum.map j id)) := by
  unfold gapRule
  rw [actualUniversalRenaming]
  change allOne (((malformed (.var (.inr 0) : OTerm (α ⊕ Fin 1))).relabel (Sum.map j id)).imp
    (θ.relabel (Sum.map j id))) = _
  rw [malformedRename]
  rfl

theorem premisesRename {α β : Type} (θ : Formula (α ⊕ Fin 1)) (j : α → β) :
    (premises θ).relabel j = premises (θ.relabel (Sum.map j id)) := by
  simp only [premises,conjunctionRename,atCodeRename,zRelabel,gapRuleRename,consRuleRename]

private theorem malformedInstantiate {α : Type} (n : OTerm α) :
    instantiate (malformed (.var (.inr 0))) (emb n) = malformed n := by
  unfold malformed nonzero
  simp only [equalEqn]
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [notSubst,eqnSubst,someConsSubst,varBind,zSubst]

theorem gapApply {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (θ : Formula (α ⊕ Fin 1)) (n : OTerm α)
    (rule : Nonempty (Derivation body Γ (gapRule θ)))
    (bad : Nonempty (Derivation body Γ (malformed n))) :
    Nonempty (Derivation body Γ (atCode θ n)) := by
  obtain ⟨rule⟩ := rule
  obtain ⟨bad⟩ := bad
  have use := Derivation.universalElimination (emb n) rule
  change Derivation body Γ (instantiate ((malformed (.var (.inr 0))).imp θ) (emb n)) at use
  rw [impInstantiate,malformedInstantiate] at use
  exact ⟨Derivation.implicationElimination use bad⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldBranchesProof
