module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnCoverageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnObserverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnFixedPointProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm trans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralRoundObserverTargets (observe Preserves)
open NumberedWindowInternalLiteralRoundObserverSyntaxProof (observeRename)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnMembersProof
open NumberedWindowInternalLiteralLeastOnEdgeProof (exact_OpenLeastOnEdge)
open NumberedWindowInternalLiteralEdgeOnCoverProof (KeepsCover)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse edgeRename)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenLeastOnFromCoverage)
open NumberedWindowInternalLiteralLeastOnObserverProof (exact_OpenLiteralSelectedObserverOn)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem casesLeastOn (C : Program 3) (E : Program 4) (s : Settings) (ctx ty seed : OTerm α) (goal : Formula α)
    (held : D B Γ (hasLeastOn C E s ctx ty seed))
    (finish : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (x : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastOnGraph C E s (ctx.relabel j) (ty.relabel j) (seed.relabel j) x) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let row := leastOnGraph C E s (ctx.relabel j) (ty.relabel j) (seed.relabel j) (.var (.inr 0))
  let Δ := row :: Γ.map weaken
  obtain ⟨witness⟩ := held
  obtain ⟨done⟩ := finish (α ⊕ Fin 1) j Δ (.var (.inr 0))
    (fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination witness done⟩

/-- The source and target of an actual edge have admitted original
scratch cover and parsed context. -/
def CoveredEndpoints (C : Program 3) (s : Settings) (E : Program 4) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b : OTerm α),
    D B Γ (acceptEdge E ctx ty a b) →
    D B Γ (coverageReport C s ctx a) ∧ D B Γ (coverageReport C s ctx b)

/-- Concrete window reports on both ends of the physically selected edge. -/
def WindowEndpoints (W : Program 3) (E : Program 4) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b : OTerm α),
    D B Γ (acceptEdge E ctx ty a b) →
    D B Γ (observe W ctx ty a (suc z)) ∧ D B Γ (observe W ctx ty b (suc z))

theorem exact_OpenObservedWindow (W : Program 3) (E : Program 4) (both : WindowEndpoints W E) :
    Preserves E W := by
  intro B α Γ ctx ty a b value edge observed
  obtain ⟨left,right⟩ := both B α Γ ctx ty a b edge
  have same := valueUnique W (suc z) value ![ctx,ty,a] left observed
  exact outputTransport W (suc z) value ![ctx,ty,b] same right

/-- The selected least program is itself a stable observer on the
actual selected edge. This is a theorem of the concrete rounds and
cover, not a recursive definition of the edge. -/
theorem exact_OpenLeastOnPreserves (count : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (E : Program 4) (s : Settings) (rev : CanReverse E)
    (sameCover : KeepsCover C s E) (endpoints : CoveredEndpoints C s E) :
    Preserves E (packedLeastOn C E s) := by
  intro B α Γ ctx ty a b value arc observed
  obtain ⟨ca,cb⟩ := endpoints B α Γ ctx ty a b arc
  have minA := exact_OpenLeastOnFromCoverage C E s ctx ty a ca
  have minB := exact_OpenLeastOnFromCoverage C E s ctx ty b cb
  apply casesLeastOn C E s ctx ty a _ minA
  intro β j Δ x keep source
  rw [observeRename]
  have rb := renameInto minB j Δ keep
  rw [hasOnRename] at rb
  have old := renameInto arc j Δ keep
  rw [edgeRename] at old
  have asked := renameInto observed j Δ keep
  rw [observeRename] at asked
  apply casesLeastOn C E s (ctx.relabel j) (ty.relabel j) (b.relabel j) _ rb
  intro γ k Θ y keep' target
  rw [observeRename]
  have hold := renameInto source k Θ keep'
  rw [leastOnRename] at hold
  have move := renameInto old k Θ keep'
  rw [edgeRename] at move
  have request := renameInto asked k Θ keep'
  rw [observeRename] at request
  let c := (ctx.relabel j).relabel k
  let t := (ty.relabel j).relabel k
  let u := (a.relabel j).relabel k
  let v := (b.relabel j).relabel k
  let chosen := x.relabel k
  let wanted := (value.relabel j).relabel k
  obtain ⟨pair⟩ := exact_OpenLeastOnEdge count strict C E s rev sameCover c t u v chosen y hold target move
  obtain ⟨identical⟩ := valueUnique (packedLeastOn C E s) (suc chosen) wanted ![c,t,u] hold request
  exact outputTransport (packedLeastOn C E s) (suc y) wanted ![c,t,v]
    ⟨trans (symm (congSuc pair)) identical⟩ target

theorem exact_OpenLeastOnFixedPoint (C : Program 3) (E : Program 4) (s : Settings)
    (paid : Preserves E (packedLeastOn C E s)) (ctx ty seed selected : OTerm α)
    (held : D B Γ (leastOnGraph C E s ctx ty seed selected)) :
    D B Γ (leastOnGraph C E s ctx ty selected selected) :=
  exact_OpenLiteralSelectedObserverOn C E s (packedLeastOn C E s) paid ctx ty seed selected (suc selected) held held

theorem exact_OpenLeastOnWindow (C : Program 3) (E : Program 4) (s : Settings) (W : Program 3)
    (ends : WindowEndpoints W E) (ctx ty seed selected : OTerm α)
    (held : D B Γ (leastOnGraph C E s ctx ty seed selected))
    (window : D B Γ (observe W ctx ty seed (suc z))) : D B Γ (observe W ctx ty selected (suc z)) :=
  exact_OpenLiteralSelectedObserverOn C E s W (exact_OpenObservedWindow W E ends)
    ctx ty seed selected (suc z) held window

#print axioms casesLeastOn
#print axioms exact_OpenLeastOnPreserves
#print axioms exact_OpenLeastOnFixedPoint
#print axioms exact_OpenLeastOnWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnFixedPointProof
