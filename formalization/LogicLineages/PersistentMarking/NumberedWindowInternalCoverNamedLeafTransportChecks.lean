module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafTransportChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (orderRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm namedReport)
open NumberedWindowInternalCoverNamedLeavesOpenProof (exact_OpenCoverNamedLeafAtLargerBound)
open NumberedWindowInternalCoverNamedLeafOriginTargets
open NumberedWindowInternalCoverNamedLeafOriginChecks (exact_OpenCoverNamedLeafOrigin)

private theorem transportKey {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (out a key : OTerm α)
    (eq : Derivation body Γ (eqn a key))
    (hit : Derivation body Γ (memberGraph out a)) :
    Nonempty (Derivation body Γ (memberGraph out key)) := by
  let clause : Formula (α ⊕ Fin 1) := memberGraph (out.relabel Sum.inl) (.var (.inr 0))
  have inst (w : OTerm α) : instantiate clause (emb w) = memberGraph out w := by
    simp only [clause,instantiate,bindEmbedding,memberSubst,liftBind,varBind]
  exact ⟨(inst key) ▸ Derivation.equalityElimination clause (emb a) (emb key) eq ((inst a).symm ▸ hit)⟩

theorem exact_OpenCoverNamedLeafTransport : ExactOpenCoverNamedLeafTransport := by
  intro b body α Γ old next K m M key small hit bound large
  have source := exact_OpenCoverNamedLeafOrigin b body α Γ old K m key small hit
  let clause := originMatrix b K m key
  let j : α → α ⊕ Fin 2 := Sum.inl
  let Δ := clause :: Γ.map (fun q => q.relabel j)
  let ty : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let i : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  apply actualFiniteExistentialElimination body α 2 Γ clause (memberGraph next key) source
  rw [graphRename]
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  have weaker := renameInto bound j Δ keep
  have target := renameInto large j Δ keep
  rw [orderRename,sucRelabel] at weaker
  simp only [namedReport,programRename,binaryInputsRename] at target
  have row : Derivation body Δ (originRow b (K.relabel j) (m.relabel j) (key.relabel j) ty i) :=
    Derivation.hypothesis List.mem_cons_self
  have tail := Derivation.conjunctionRight row
  obtain ⟨found⟩ := exact_OpenCoverNamedLeafAtLargerBound b body (α ⊕ Fin 2) Δ
    (next.relabel j) (K.relabel j) ty i (m.relabel j) (M.relabel j) ⟨Derivation.conjunctionLeft row⟩
    ⟨Derivation.conjunctionLeft tail⟩ weaker target
  exact transportKey (next.relabel j) (namedTerm b.toNat ty i) (key.relabel j)
    (Derivation.conjunctionRight tail) found

#print axioms exact_OpenCoverNamedLeafTransport

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafTransportChecks
