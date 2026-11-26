module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastFixedPointProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename binder occurrenceUnfold)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph poolOccurrence)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed membersAtSeed)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalLiteralRoundLeastTargets
open NumberedWindowInternalLiteralRoundLeastInductionProof (allCounts)
open NumberedWindowInternalLiteralRoundLeastSyntaxProof (applyAt)
open NumberedWindowInternalSparsePackedLeastOpenChecks (exact_OpenPackedLeastPoolOccurrence)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

theorem exact_LiteralRoundLeast : ExactRoundLeast := by
  intro C X W s paid body α Γ i vertices ctx ty seed out k m
  let A := inputs C X W s i vertices ctx ty seed out k m
  obtain ⟨d⟩ := applyAt (body := body) (Delta := A :: Γ) C X W s i vertices ctx ty seed out k m
    (allCounts C X W s paid i) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

private theorem atLength (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (ctx ty seed m vertices pool : OTerm α)
    (least : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed m)))
    (hit : Nonempty (Derivation body Γ (memberGraph pool m)))
    (computed : Nonempty (Derivation body Γ (programGraph (members (edge4 X W)) pool (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (leastGraph C X W s ctx ty m m)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep length
  rw [leastRename]
  rw [unaryInputsRename] at length
  have value := renameInto least j Δ keep
  rw [leastRename] at value
  have g := renameInto hit j Δ keep
  rw [graphRename] at g
  have ss := renameInto computed j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at ss
  obtain ⟨atLen⟩ := exact_OpenMembersAtLength (edge4 X W) body β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨rule⟩ := exact_LiteralRoundLeast C X W s paid body β Δ fuel (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) (pool.relabel j) (m.relabel j) (m.relabel j)
  obtain ⟨l⟩ := length
  obtain ⟨v⟩ := ss
  obtain ⟨g⟩ := g
  obtain ⟨value⟩ := value
  have run := Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination atLen l)) v
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction value (Derivation.conjunctionIntroduction run g))⟩


/-- Recover the actual cover bound and its directed rounds from the
physical pool reported by the original minimum. -/
private theorem fromMembers (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (ctx ty seed m pool : OTerm α)
    (least : D body Γ (leastGraph C X W s ctx ty seed m))
    (hit : D body Γ (memberGraph pool m))
    (computed : D body Γ (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed])) :
    D body Γ (leastGraph C X W s ctx ty m m) := by
  apply programCases (poolAtSeed C s) ![ctx,ty,seed] _
  intro β j Δ vertices keep vv
  rw [leastRename]
  rw [tripleInputsRename] at vv
  have old := renameInto least j Δ keep
  rw [leastRename] at old
  have selected := renameInto hit j Δ keep
  rw [graphRename] at selected
  have ss := renameInto computed j Δ keep
  rw [programRename,tripleInputsRename] at ss
  let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
  apply atLength C X W s paid (ctx.relabel j) (ty.relabel j) (seed.relabel j) (m.relabel j)
    vertices (pool.relabel j) old selected
  apply compositionRecover (members (edge4 X W)) ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    (pool.relabel j) xs (membersTape vertices (ctx.relabel j) (ty.relabel j) (seed.relabel j)) ss
  intro k
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
  · exact vv
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero c
    exact projectionValue 2 xs

/-- Exact least idempotence in any one fixed presentation from the
single real exchange-edge preservation obligation. The chosen minimum
is proved to occur in its actual pool, and the computed length and
open finite-round induction are used without positing a decoded list. -/
theorem exact_LiteralLeastFixedPointFromEdge (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (paid : SameLeastOnEdge C X W s) (ctx ty seed m : OTerm α)
    (least : D body Γ (leastGraph C X W s ctx ty seed m)) :
    D body Γ (leastGraph C X W s ctx ty m m) := by
  obtain ⟨rule⟩ := exact_OpenPackedLeastPoolOccurrence body α Γ C X W s ctx ty seed m
  obtain ⟨source⟩ := least
  have occ : D body Γ (poolOccurrence C X W s ctx ty seed m) :=
    ⟨Derivation.implicationElimination rule source⟩
  rw [occurrenceUnfold] at occ
  let a := binder C X W s ctx ty seed m
  let Δ := existsOne a :: Γ.map weaken
  let Θ := a :: Δ.map weaken
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 := Sum.inl
  let lift := fun (x : OTerm α) => (x.relabel j).relabel k
  let pool : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  have first := renameInto (⟨source⟩ : D body Γ (leastGraph C X W s ctx ty seed m)) j Δ
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  have second := renameInto first k Θ
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [leastRename,leastRename] at second
  have atPool : Derivation body Θ a := Derivation.hypothesis List.mem_cons_self
  have row := Derivation.conjunctionRight atPool
  obtain ⟨chosen⟩ := fromMembers C X W s paid (lift ctx) (lift ty) (lift seed) (lift m) pool
    second ⟨Derivation.conjunctionRight row⟩ ⟨Derivation.conjunctionLeft row⟩
  have final : Derivation body Θ (weaken (weaken (leastGraph C X W s ctx ty m m))) := by
    change Derivation body Θ (((leastGraph C X W s ctx ty m m).relabel j).relabel k)
    rw [leastRename,leastRename]
    exact chosen
  have closeInner : Derivation body Δ (weaken (leastGraph C X W s ctx ty m m)) :=
    Derivation.existentialElimination (Derivation.hypothesis List.mem_cons_self) final
  obtain ⟨both⟩ := occ
  exact ⟨Derivation.existentialElimination both closeInner⟩

#print axioms exact_LiteralRoundLeast
#print axioms exact_LiteralLeastFixedPointFromEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastFixedPointProof
