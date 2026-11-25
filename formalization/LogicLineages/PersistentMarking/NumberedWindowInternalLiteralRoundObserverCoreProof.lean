module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverCoreProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn z suc sucRelabel bindEmbedding liftBind varBind)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralRoundObserverTargets (inputs observe Preserves)
open NumberedWindowInternalLiteralRoundObserverSyntaxProof (AtCount applyAt atCountRename observeSubst observeRename)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRoundOriginChecks (exact_ZeroRoundOrigin exact_SuccessorRoundOrigin)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalSparseDirectedSeen (seenWitness witnessRow acceptEdge)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (witnessBinder witnessUnfold)
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (E : Program 4) (O : Program 3)

private theorem moveObserver (ctx ty w k m : OTerm α) (same : Derivation body Γ (eqn w k))
    (d : Derivation body Γ (observe O ctx ty w m)) : Nonempty (Derivation body Γ (observe O ctx ty k m)) := by
  let θ : Formula (α ⊕ Fin 1) := observe O (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr 0)) (m.relabel Sum.inl)
  have inst (x : OTerm α) : instantiate θ (emb x) = observe O ctx ty x m := by
    simp only [θ,instantiate,bindEmbedding,observeSubst,liftBind,varBind]
  have moved := Derivation.equalityElimination θ (emb w) (emb k) same (by rw [inst]; exact d)
  rw [inst] at moved
  exact ⟨moved⟩

theorem baseCore (vertices ctx ty seed out k m : OTerm α)
    (h : Derivation body Γ (inputs E O z vertices ctx ty seed out k m)) :
    Nonempty (Derivation body Γ (observe O ctx ty k m)) := by
  obtain ⟨origin⟩ := exact_ZeroRoundOrigin exact_RetainedPredecessor E body α Γ out vertices ctx ty seed k
  have r := Derivation.conjunctionRight h
  have given := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination origin (Derivation.conjunctionLeft r))) (Derivation.conjunctionRight r)
  exact moveObserver O ctx ty seed k m (Derivation.conjunctionRight given) (Derivation.conjunctionLeft h)

private theorem fromWitness (paid : Preserves E O) (i vertices ctx ty seed before k m : OTerm α)
    (old : Nonempty (Derivation body Γ (AtCount E O i)))
    (selected : Nonempty (Derivation body Γ (observe O ctx ty seed m)))
    (prior : Nonempty (Derivation body Γ (roundGraph E before i vertices ctx ty seed)))
    (witness : Derivation body Γ (seenWitness E before ctx ty k)) :
    Nonempty (Derivation body Γ (observe O ctx ty k m)) := by
  rw [witnessUnfold] at witness
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Δ := witnessBinder E before ctx ty k :: Γ.map weaken
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have old' := renameInto old j Δ keep
  have selected' := renameInto selected j Δ keep
  have prior' := renameInto prior j Δ keep
  rw [atCountRename] at old'
  rw [observeRename O] at selected'
  rw [roundRename] at prior'
  obtain ⟨selected'⟩ := selected'
  obtain ⟨prior'⟩ := prior'
  have row : Derivation body Δ (witnessRow E (before.relabel j) (ctx.relabel j) (ty.relabel j) w (k.relabel j)) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨atW⟩ := applyAt E O (i.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (before.relabel j) w (m.relabel j) old' ⟨Derivation.conjunctionIntroduction selected'
      (Derivation.conjunctionIntroduction prior' (Derivation.conjunctionLeft row))⟩
  let eq := eqn w (k.relabel j)
  let edge := acceptEdge E (ctx.relabel j) (ty.relabel j) w (k.relabel j)
  obtain ⟨a⟩ := moveObserver (Γ := eq :: Δ) O (ctx.relabel j) (ty.relabel j) w (k.relabel j) (m.relabel j)
    (Derivation.hypothesis List.mem_cons_self) (addHyp atW eq)
  obtain ⟨b⟩ := paid body _ (edge :: Δ) (ctx.relabel j) (ty.relabel j) w (k.relabel j) (m.relabel j)
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp atW edge⟩
  have result := disjunctionElimination (Derivation.conjunctionRight row)
    (Derivation.implicationIntroduction a) (Derivation.implicationIntroduction b)
  have final : Derivation body Δ (weaken (observe O ctx ty k m)) := by
    change Derivation body Δ ((observe O ctx ty k m).relabel j)
    rwa [observeRename O]
  exact ⟨Derivation.existentialElimination witness final⟩

theorem stepCore (paid : Preserves E O) (i vertices ctx ty seed out k m : OTerm α)
    (old : Nonempty (Derivation body Γ (AtCount E O i)))
    (input : Nonempty (Derivation body Γ (inputs E O (suc i) vertices ctx ty seed out k m))) :
    Nonempty (Derivation body Γ (observe O ctx ty k m)) := by
  apply programCases (rounds E) (roundsTape i vertices ctx ty seed) _
  intro β j Δ before keep prior
  rw [observeRename O]
  have ih := renameInto old j Δ keep
  rw [atCountRename] at ih
  have h := renameInto input j Δ keep
  simp only [inputs,conjunctionRename,observeRename,roundRename,sucRelabel,graphRename] at h
  obtain ⟨h⟩ := h
  have tape : (fun k => (roundsTape i vertices ctx ty seed k).relabel j) =
      roundsTape (i.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
    funext k
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
      Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.elim0 e) d) c) b) a) k <;> rfl
  rw [tape] at prior
  obtain ⟨p⟩ := prior
  obtain ⟨law⟩ := exact_SuccessorRoundOrigin exact_RetainedPredecessor E body β Δ before
    (out.relabel j) (i.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (k.relabel j)
  have r := Derivation.conjunctionRight h
  have found := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination law (Derivation.conjunctionIntroduction p (Derivation.conjunctionLeft r))))
    (Derivation.conjunctionRight r)
  exact fromWitness E O paid _ _ _ _ _ before _ _ ih ⟨Derivation.conjunctionLeft h⟩ ⟨p⟩ (Derivation.conjunctionRight found)

#print axioms baseCore
#print axioms stepCore
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverCoreProof
