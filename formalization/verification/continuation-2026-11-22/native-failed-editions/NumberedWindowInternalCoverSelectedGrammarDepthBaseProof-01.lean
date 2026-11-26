module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsConstructorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc eqn eqnRelabel zRelabel sucRelabel bindEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange rangeReport)
open NumberedWindowInternalCoverAscendingRangeOriginDataProof (nilHit)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion cellsAt cellsReport)
open NumberedWindowInternalCoverArgumentCellsTransportProof (axisRename)
open NumberedWindowInternalCoverArgumentCellsOpenDataProof (unaryTapeRename)
open NumberedWindowInternalCoverArgumentCellsConstructorProof (sentinel)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport stepTape argsPart)
open NumberedWindowInternalCoverSelectedGrammarOpenBaseProof (exact_OpenSelectedGrammarBaseSplit)
open NumberedWindowInternalCoverSelectedGrammarOpenStepProof (exact_OpenSelectedGrammarSuccessorSplit)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets
open NumberedWindowInternalCoverSelectedGrammarDepthBindingProof (buildDepth)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}

theorem inclusionRename (t t' a a' : OTerm α) (j : α → β) :
    (pairInclusion t t' a a').relabel j =
      pairInclusion (t.relabel j) (t'.relabel j) (a.relabel j) (a'.relabel j) := by
  unfold pairInclusion
  rw [conjunctionRename,axisRename,axisRename]

private theorem fromEmpty (old next : OTerm α)
    (empty : Nonempty (Derivation body Γ (eqn z old))) :
    Nonempty (Derivation body Γ (axisInclusion old next)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let m := memberGraph (old.relabel j) key
  let Δ := m :: Γ.map (fun p => p.relabel j)
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := renameInto empty j Δ keep
  rw [eqnRelabel,zRelabel] at he
  obtain ⟨he⟩ := he
  have impossible := headTransport scratchMember (suc z) (old.relabel j) z ![key] ⟨symm he⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨bottom⟩ := nilHit key impossible
  exact ⟨Derivation.universalIntroduction
    (Derivation.implicationIntroduction (Derivation.explosion bottom))⟩

private theorem moveKey (out a key : OTerm α)
    (eq : Derivation body Γ (eqn a key))
    (hit : Derivation body Γ (memberGraph out a)) :
    Derivation body Γ (memberGraph out key) := by
  let clause : Formula (α ⊕ Fin 1) := memberGraph (out.relabel Sum.inl) (.var (.inr 0))
  have inst (w : OTerm α) : instantiate clause (emb w) = memberGraph out w := by
    simp only [clause,instantiate,bindEmbedding,memberSubst,liftBind,varBind]
  exact (inst key) ▸ Derivation.equalityElimination clause (emb a) (emb key) eq ((inst a).symm ▸ hit)

private theorem singletonKey (old next key : OTerm α)
    (small : Nonempty (Derivation body Γ (consGraph old z z)))
    (hit : Nonempty (Derivation body Γ (memberGraph old key)))
    (zero : Nonempty (Derivation body Γ (memberGraph next z))) :
    Nonempty (Derivation body Γ (memberGraph next key)) := by
  obtain ⟨which⟩ := consInversion old z z key small hit
  let L := (missGraph z key).not
  let R := memberGraph z key
  obtain ⟨eq⟩ := nonzeroEquality (body := body) (Γ := L :: Γ) z key
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨present⟩ := withHyp zero L
  obtain ⟨bottom⟩ := nilHit (body := body) (Γ := R :: Γ) key
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination which (Derivation.implicationIntroduction (moveKey next z key eq present))
    (Derivation.implicationIntroduction (Derivation.explosion bottom))⟩

private theorem fromSingleton (old next : OTerm α)
    (small : Nonempty (Derivation body Γ (consGraph old z z)))
    (zero : Nonempty (Derivation body Γ (memberGraph next z))) :
    Nonempty (Derivation body Γ (axisInclusion old next)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let m := memberGraph (old.relabel j) key
  let Δ := m :: Γ.map (fun p => p.relabel j)
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have old' := renameInto small j Δ keep
  have zero' := renameInto zero j Δ keep
  rw [consGraphRename,zRelabel] at old'
  rw [graphRename,zRelabel] at zero'
  obtain ⟨found⟩ := singletonKey (old.relabel j) (next.relabel j) key old'
    ⟨Derivation.hypothesis List.mem_cons_self⟩ zero'
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction found)⟩

private theorem fromArgs (out H K ids t a : OTerm α)
    (run : Nonempty (Derivation body Γ (stepReport argsPart out H K ids t a))) :
    Nonempty (Derivation body Γ (cellsReport out t a)) := by
  let xs := stepTape H K ids t a
  let slots : Fin 2 → Fin 5 := ![3,4]
  have got := recoverReordered cellsAt slots out xs run
  have tape : (fun i => xs (slots i)) = ![t,a] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [tape] at got
  exact got

private theorem baseWithRange (H K M ids old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (small : Nonempty (Derivation body Γ (observed z H K M old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed (suc z) H K M next nextTerms nextArgs)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M)))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  obtain ⟨s⟩ := small
  obtain ⟨l⟩ := large
  have reads := Derivation.conjunctionRight s
  have nextReads := Derivation.conjunctionRight l
  obtain ⟨base⟩ := exact_OpenSelectedGrammarBaseSplit body α Γ old oldTerms oldArgs H K M
    ⟨Derivation.conjunctionLeft s⟩ ⟨Derivation.conjunctionLeft reads⟩ ⟨Derivation.conjunctionRight reads⟩
  obtain ⟨step⟩ := exact_OpenSelectedGrammarSuccessorSplit body α Γ old next z H K M ids
    oldTerms oldArgs nextTerms nextArgs ⟨Derivation.conjunctionLeft s⟩ ⟨Derivation.conjunctionLeft l⟩
    ⟨Derivation.conjunctionLeft reads⟩ ⟨Derivation.conjunctionRight reads⟩ range
    ⟨Derivation.conjunctionLeft nextReads⟩ ⟨Derivation.conjunctionRight nextReads⟩
  have args := fromArgs nextArgs H K ids oldTerms oldArgs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight step)⟩
  obtain ⟨includeTerms⟩ := fromEmpty oldTerms nextTerms ⟨Derivation.conjunctionLeft base⟩
  obtain ⟨includeArgs⟩ := fromSingleton oldArgs nextArgs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight base)⟩
    (sentinel nextArgs oldTerms oldArgs args)
  exact ⟨Derivation.conjunctionIntroduction includeTerms includeArgs⟩

private theorem atBase (H K M old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (small : Nonempty (Derivation body Γ (observed z H K M old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed (suc z) H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  apply programCases ascendingRange ![suc M] _
  intro β j Δ ids keep actual
  rw [inclusionRename]
  simp only [unaryTapeRename,sucRelabel] at actual
  have old' := renameInto small j Δ keep
  have next' := renameInto large j Δ keep
  rw [observedRename,zRelabel] at old'
  rw [observedRename,sucRelabel,zRelabel] at next'
  exact baseWithRange (H.relabel j) (K.relabel j) (M.relabel j) ids
    (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j)
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) old' next' actual

theorem adjacentAtZero (H K M : OTerm α) :
    Nonempty (Derivation body Γ (adjacentAt z H K M)) := by
  apply buildDepth z (suc z) H K M
  intro β j Δ old oldTerms oldArgs next nextTerms nextArgs keep small large
  simp only [sucRelabel,zRelabel] at small large
  exact atBase (H.relabel j) (K.relabel j) (M.relabel j)
    old oldTerms oldArgs next nextTerms nextArgs small large

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBaseProof
