module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (existsEmbeddedSubst liftTermSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst consTermSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind sucRelabel sucSubst zSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalDirectTargetMapIntroTargets

attribute [local irreducible] programGraph

private theorem singletonSubst {α β : Type} (a : OTerm α) (σ : α → OTerm β) :
    (fun i : Fin 1 => ((![a] : Fin 1 → OTerm α) i).subst σ) = ![a.subst σ] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem projectedRename {α β : Type} (q rows : OTerm α) (j : α → β) :
    (unary scratchTargets (suc q) rows).relabel j =
      unary scratchTargets (suc (q.relabel j)) (rows.relabel j) := by
  rw [unaryRename,sucRelabel]

private theorem projectedSubst {α β : Type} (q rows : OTerm α) (σ : α → OTerm β) :
    (unary scratchTargets (suc q) rows).subst (fun i => emb (σ i)) =
      unary scratchTargets (suc (q.subst σ)) (rows.subst σ) := by
  simp only [unary,programSubst,sucSubst,singletonSubst]

theorem hasRename {α β : Type} (rows : OTerm α) (j : α → β) :
    (hasProjection rows).relabel j = hasProjection (rows.relabel j) := by
  unfold hasProjection
  rw [existsRename]
  let rho : α ⊕ Fin 1 → β ⊕ Fin 1 := Sum.map j id
  have slots : (projectedBody rows).relabel rho = projectedBody (rows.relabel j) := by
    unfold projectedBody
    rw [projectedRename]
    have first : (Term.var (.inr (0 : Fin 1)) : OTerm (α ⊕ Fin 1)).relabel rho =
        (Term.var (.inr (0 : Fin 1)) : OTerm (β ⊕ Fin 1)) := rfl
    have second : (rows.relabel Sum.inl).relabel rho = (rows.relabel j).relabel Sum.inl := by
      rw [Term.relabel_relabel,Term.relabel_relabel]
      rfl
    rw [first,second]
  rw [slots]

private theorem hasSubst {α β : Type} (rows : OTerm α) (σ : α → OTerm β) :
    (hasProjection rows).subst (fun i => emb (σ i)) = hasProjection (rows.subst σ) := by
  simp only [hasProjection,projectedBody,existsEmbeddedSubst,projectedSubst,liftTermSubst]
  rfl

private theorem loopSubst {α β : Type} (r : Program 3) (rows raw : OTerm α) (σ : α → OTerm β) :
    (loopAccept r rows raw).subst (fun i => emb (σ i)) =
      loopAccept r (rows.subst σ) (raw.subst σ) := by
  simp only [loopAccept,recGraph,programSubst,consTermSubst,singletonSubst,oneTerm,
    NumberedWindowInternalDirectInsertedRowTargets.Zero,sucSubst,zSubst]

private theorem atSubst {α β : Type} (r : Program 3) (rows raw : OTerm α) (σ : α → OTerm β) :
    (atRows r rows raw).subst (fun i => emb (σ i)) = atRows r (rows.subst σ) (raw.subst σ) := by
  simp only [atRows,impSubst,loopSubst,hasSubst]

private theorem atRename {α β : Type} (r : Program 3) (rows raw : OTerm α) (j : α → β) :
    (atRows r rows raw).relabel j = atRows r (rows.relabel j) (raw.relabel j) := by
  simp only [atRows,impRename,loopRename,hasRename]

theorem motiveCode {α : Type} (r : Program 3) (rows raw : OTerm α) :
    atCode (motive r raw) rows = atRows r rows raw := by
  rw [atCode,instantiate,bindEmbedding]
  unfold motive
  rw [atSubst]
  simp only [liftBind,varBind]

theorem motiveIndex {α : Type} (r : Program 3) (raw : OTerm α) (i : Fin 3) :
    atIndex (motive r raw) i = atRows r (.var (.inr i)) (raw.relabel Sum.inl) := by
  unfold atIndex motive
  rw [atRename]
  simp only [Term.relabel_relabel]
  rfl

theorem projectionWitness {α : Type} (q rows : OTerm α) :
    instantiate (projectedBody rows) (emb q) = unary scratchTargets (suc q) rows := by
  rw [projectedBody,instantiate,bindEmbedding,projectedSubst]
  simp only [liftBind,varBind]

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem projectionIntro (q rows : OTerm α) (h : D B Γ (unary scratchTargets (suc q) rows)) :
    D B Γ (hasProjection rows) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb q)
  rw [projectionWitness]
  exact h

theorem projectionCases (rows : OTerm α) (psi : Formula α) (h : D B Γ (hasProjection rows))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (unary scratchTargets (suc out) (rows.relabel j)) →
      D B Δ (psi.relabel j)) : D B Γ psi := by
  obtain ⟨h⟩ := h
  let j : α → α ⊕ Fin 1 := Sum.inl
  let q : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Δ := projectedBody rows :: Γ.map (fun f => f.relabel j)
  obtain ⟨d⟩ := k (α ⊕ Fin 1) j Δ q
    (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

#print axioms projectionCases

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroSyntaxProof
