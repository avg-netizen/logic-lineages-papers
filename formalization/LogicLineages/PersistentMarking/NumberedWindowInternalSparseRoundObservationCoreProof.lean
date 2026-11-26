module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationCoreProof
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
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseCoveredInstallationTargets (SameLeastOnEdge)
open NumberedWindowInternalSparseRoundObservationTargets (inputs observed source)
open NumberedWindowInternalSparseRoundObservationSyntaxProof (AtCount applyAt atCountRename observedSubst observedRename sourceRename applyEdge)
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
variable (E : Program 4) (M : Program 5)

private theorem moveValue (ctx dom cod arg w k m : OTerm α) (same : Derivation body Γ (eqn w k))
    (d : Derivation body Γ (observed M ctx dom cod arg w m)) : Nonempty (Derivation body Γ (observed M ctx dom cod arg k m)) :=
  ID1Completion.InternalControlGraphSupportProof.headTransport M m w k ![ctx,dom,cod,arg] ⟨same⟩ ⟨d⟩

theorem baseCore (vertices ctx ty seed out k m dom cod arg : OTerm α)
    (h : Derivation body Γ (inputs E M z vertices ctx ty seed out k m dom cod arg)) :
    Nonempty (Derivation body Γ (observed M ctx dom cod arg k m)) := by
  obtain ⟨origin⟩ := exact_ZeroRoundOrigin exact_RetainedPredecessor E body α Γ out vertices ctx ty seed k
  have r := Derivation.conjunctionRight h
  have given := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination origin (Derivation.conjunctionLeft r))) (Derivation.conjunctionRight r)
  exact moveValue M ctx dom cod arg seed k m (Derivation.conjunctionRight given) (Derivation.conjunctionRight (Derivation.conjunctionLeft h))

private theorem fromWitness (i vertices ctx ty seed before k m dom cod arg : OTerm α)
    (old : Nonempty (Derivation body Γ (AtCount E M i)))
    (selected : Nonempty (Derivation body Γ (source E M ctx ty dom cod arg seed m)))
    (prior : Nonempty (Derivation body Γ (roundGraph E before i vertices ctx ty seed)))
    (witness : Derivation body Γ (seenWitness E before ctx ty k)) :
    Nonempty (Derivation body Γ (observed M ctx dom cod arg k m)) := by
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
  rw [sourceRename] at selected'
  rw [roundRename] at prior'
  obtain ⟨selected'⟩ := selected'
  obtain ⟨prior'⟩ := prior'
  have row : Derivation body Δ (witnessRow E (before.relabel j) (ctx.relabel j) (ty.relabel j) w (k.relabel j)) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨atW⟩ := applyAt E M (i.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (before.relabel j) w (m.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) old' ⟨Derivation.conjunctionIntroduction selected'
      (Derivation.conjunctionIntroduction prior' (Derivation.conjunctionLeft row))⟩
  let eq := eqn w (k.relabel j)
  let edge := acceptEdge E (ctx.relabel j) (ty.relabel j) w (k.relabel j)
  obtain ⟨a⟩ := moveValue (Γ := eq :: Δ) M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) w (k.relabel j) (m.relabel j)
    (Derivation.hypothesis List.mem_cons_self) (addHyp atW eq)
  obtain ⟨b⟩ := applyEdge (Γ := edge :: Δ) E M (ctx.relabel j) (ty.relabel j)
    (dom.relabel j) (cod.relabel j) (arg.relabel j) (m.relabel j) w (k.relabel j)
    ⟨addHyp (Derivation.conjunctionLeft selected') edge⟩ (Derivation.hypothesis List.mem_cons_self) (addHyp atW edge)
  have result := disjunctionElimination (Derivation.conjunctionRight row)
    (Derivation.implicationIntroduction a) (Derivation.implicationIntroduction b)
  have final : Derivation body Δ (weaken (observed M ctx dom cod arg k m)) := by
    change Derivation body Δ ((observed M ctx dom cod arg k m).relabel j)
    rwa [observedRename]
  exact ⟨Derivation.existentialElimination witness final⟩

theorem stepCore (i vertices ctx ty seed out k m dom cod arg : OTerm α)
    (old : Nonempty (Derivation body Γ (AtCount E M i)))
    (input : Nonempty (Derivation body Γ (inputs E M (suc i) vertices ctx ty seed out k m dom cod arg))) :
    Nonempty (Derivation body Γ (observed M ctx dom cod arg k m)) := by
  apply programCases (rounds E) (roundsTape i vertices ctx ty seed) _
  intro β j Δ before keep prior
  rw [observedRename]
  have ih := renameInto old j Δ keep
  rw [atCountRename] at ih
  have h := renameInto input j Δ keep
  simp only [inputs,conjunctionRename,sourceRename,roundRename,sucRelabel,graphRename] at h
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
  exact fromWitness E M _ _ _ _ _ before _ _ _ _ _ ih ⟨Derivation.conjunctionLeft h⟩ ⟨p⟩ (Derivation.conjunctionRight found)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationCoreProof
