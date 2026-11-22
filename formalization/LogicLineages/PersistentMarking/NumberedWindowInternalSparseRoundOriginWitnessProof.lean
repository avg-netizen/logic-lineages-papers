module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginWitnessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel z zRelabel suc emb bindEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply trans)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalSparseScratchMembership (memberStep memberBase)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseDirectedSeen (seenWitness witnessRow acceptEdge edgeTape)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (witnessUnfold witnessBinder)
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveMember (vertices a b : OTerm α) (equal : Derivation body Γ (eqn a b))
    (present : Derivation body Γ (memberGraph vertices a)) : Nonempty (Derivation body Γ (memberGraph vertices b)) := by
  let θ : Formula (α ⊕ Fin 1) := memberGraph (vertices.relabel Sum.inl) (.var (.inr 0))
  have inst (x : OTerm α) : instantiate θ (emb x) = memberGraph vertices x := by
    simp only [θ,instantiate,bindEmbedding,memberSubst,liftBind,varBind]
  have result := Derivation.equalityElimination θ (emb a) (emb b) equal (by rw [inst]; exact present)
  rw [inst] at result
  exact ⟨result⟩

private theorem uniqueHead (code seed k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code seed z)))
    (present : Nonempty (Derivation body Γ (memberGraph code k))) :
    Nonempty (Derivation body Γ (eqn seed k)) := by
  obtain ⟨split⟩ := consInversion code seed z k cell present
  let P := (missGraph seed k).not
  let Q := memberGraph z k
  obtain ⟨yes⟩ := nonzeroEquality (body := body) (Γ := P :: Γ) seed k (Derivation.hypothesis List.mem_cons_self)
  have nilRun := nilRecover (body := body) (Gamma := Q :: Γ) memberBase memberStep (suc z)
    (![k] : Fin 1 → OTerm α) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨impossible⟩ := valueUnique memberBase (suc z) z (![k] : Fin 1 → OTerm α) nilRun (zeroConstantValue _)
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction yes)
    (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply impossible)))⟩

theorem singletonOrigin (code seed ctx ty k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code seed z)))
    (witness : Derivation body Γ (seenWitness (constantZero 4) code ctx ty k)) :
    Nonempty (Derivation body Γ (eqn seed k)) := by
  rw [witnessUnfold] at witness
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Θ := witnessBinder (constantZero 4) code ctx ty k :: Γ.map weaken
  have rr : Derivation body Θ (witnessRow (constantZero 4) (code.relabel j)
      (ctx.relabel j) (ty.relabel j) w (k.relabel j)) := Derivation.hypothesis List.mem_cons_self
  have c := renameInto cell j Θ (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [consGraphRename,zRelabel] at c
  obtain ⟨first⟩ := uniqueHead _ _ w c ⟨Derivation.conjunctionLeft rr⟩
  let A := eqn w (k.relabel j)
  let B := acceptEdge (constantZero 4) (ctx.relabel j) (ty.relabel j) w (k.relabel j)
  have yes := trans (addHyp first A) (Derivation.hypothesis List.mem_cons_self : Derivation body (A :: Θ) A)
  obtain ⟨bad⟩ := valueUnique (body := body) (Gamma := B :: Θ) (constantZero 4) (suc z) z
    (edgeTape (ctx.relabel j) (ty.relabel j) w (k.relabel j)) ⟨Derivation.hypothesis List.mem_cons_self⟩ (zeroConstantValue _)
  have atW : Derivation body Θ (eqn (seed.relabel j) (k.relabel j)) :=
    disjunctionElimination (Derivation.conjunctionRight rr) (Derivation.implicationIntroduction yes)
      (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply bad)))
  have final : Derivation body Θ (weaken (eqn seed k)) := by
    change Derivation body Θ ((eqn seed k).relabel j)
    rwa [eqnRelabel]
  exact ⟨Derivation.existentialElimination witness final⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginWitnessProof
