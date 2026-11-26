module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalScratchCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb zRelabel zSubst sucRelabel sucSubst eqn eqnRelabel bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph scratchGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopRename)
open NumberedWindowInternalSparsePositiveIterationBindingProof (loopSubst scratchRename)
open NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof (scratchSubst)
open NumberedWindowInternalSparsePositiveOpenCharacterizationTargets

attribute [local irreducible] programGraph positive

def acceptance {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) : Formula α :=
  programGraph (positive raw least) (suc z) (args5 ctx ty source cert target)

def certificateResult {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) : Formula α :=
  (eqn cert z).not ⊓ successfulTerminal raw least ctx ty source cert target

private theorem argsRename {α β : Type} (ctx ty source cert target : OTerm α) (j : α → β) :
    (fun i => (args5 ctx ty source cert target i).relabel j) =
      args5 (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j) (target.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun d =>
    Fin.cases ?_ (fun e => Fin.cases ?_ (fun u => Fin.elim0 u) e) d) b) a) i <;> rfl

theorem acceptanceRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) (j : α → β) :
    (acceptance raw least ctx ty source cert target).relabel j =
      acceptance raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j) (target.relabel j) := by
  unfold acceptance
  rw [programRename,argsRename,sucRelabel,zRelabel]

theorem successRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) (j : α → β) :
    (successfulTerminal raw least ctx ty source cert target).relabel j =
      successfulTerminal raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j)
        (target.relabel j) := by
  unfold successfulTerminal targetScratchRow
  rw [existsRename]
  simp only [conjunctionRename,loopRename,scratchRename,sucRelabel,zRelabel,Term.relabel_relabel,
    Term.relabel] <;> rfl

theorem resultRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) (j : α → β) :
    (certificateResult raw least ctx ty source cert target).relabel j =
      certificateResult raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j)
        (target.relabel j) := by
  unfold certificateResult
  rw [conjunctionRename,successRename]
  change ((eqn cert z).relabel j).not ⊓ _ = _
  rw [eqnRelabel,zRelabel]

private theorem targetWitness {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target state : OTerm α) :
    instantiate (targetScratchRow raw least ctx ty source cert target) (emb state) =
      loopGraph raw least state cert ctx ty (suc source) cert ⊓ scratchGraph state z (suc target) := by
  simp only [targetScratchRow,instantiate,bindEmbedding,conjunctionSubst,loopSubst,scratchSubst,
    liftBind,varBind,sucSubst,zSubst]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem provideState (raw : Program 5) (least : Program 3) (ctx ty source cert target state : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state cert ctx ty (suc source) cert)))
    (scratch : Nonempty (Derivation body Γ (scratchGraph state z (suc target)))) :
    Nonempty (Derivation body Γ (successfulTerminal raw least ctx ty source cert target)) := by
  obtain ⟨l⟩ := loop
  obtain ⟨s⟩ := scratch
  exact ⟨Derivation.existentialIntroduction (phi := targetScratchRow raw least ctx ty source cert target)
    (emb state) ((targetWitness raw least ctx ty source cert target state).symm ▸
      Derivation.conjunctionIntroduction l s)⟩

theorem targetCases (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (goal : Formula α)
    (done : Nonempty (Derivation body Γ (successfulTerminal raw least ctx ty source cert target)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (loopGraph raw least state (cert.relabel j)
        (ctx.relabel j) (ty.relabel j) (suc (source.relabel j)) (cert.relabel j))) →
      Nonempty (Derivation body Δ (scratchGraph state z (suc (target.relabel j)))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨done⟩ := done
  let j : α → α ⊕ Fin 1 := Sum.inl
  let state : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := targetScratchRow raw least ctx ty source cert target
  let Δ := row :: Γ.map weaken
  have hJ (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have d : Derivation body Δ row := Derivation.hypothesis List.mem_cons_self
  obtain ⟨use⟩ := k (α ⊕ Fin 1) j Δ state hJ ⟨Derivation.conjunctionLeft d⟩ ⟨Derivation.conjunctionRight d⟩
  exact ⟨Derivation.existentialElimination done use⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof
