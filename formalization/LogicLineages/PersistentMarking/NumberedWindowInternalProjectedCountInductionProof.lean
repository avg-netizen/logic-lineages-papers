module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountEitherSideProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalProjectedCountNilProof (exact_OpenProjectedCountNil)
open NumberedWindowInternalProjectedCountEitherSideProof (exact_ProjectedCountOnLeft exact_ProjectedCountOnRight)
open NumberedWindowInternalProjectedCountInductionConsProof (exact_OpenProjectedCountInductionCons)
open NumberedWindowInternalProjectedCountInductionSyntaxProof
  (atRowsRename motiveAtCode motiveAtIndex applyAtRows)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalProjectedCountInductionTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilAt (pool : OTerm α) : D B Γ (atRows z pool) := by
  apply actualFiniteUniversalIntroduction B α 6 Γ (matrix z pool)
  let j : α → α ⊕ Fin 6 := Sum.inl
  let G := Γ.map (fun p => p.relabel j)
  let fl : OTerm (α ⊕ Fin 6) := .var (.inr 0)
  let fr : OTerm (α ⊕ Fin 6) := .var (.inr 1)
  let p : OTerm (α ⊕ Fin 6) := .var (.inr 2)
  let pl : OTerm (α ⊕ Fin 6) := .var (.inr 3)
  let pr : OTerm (α ⊕ Fin 6) := .var (.inr 4)
  let joined : OTerm (α ⊕ Fin 6) := .var (.inr 5)
  change D B G (consequent (z.relabel j) (pool.relabel j) fl fr p pl pr joined)
  rw [zRelabel]
  let S := reportMatrix z (pool.relabel j) fl fr p pl pr joined
  let Δ := S :: G
  have h : Derivation B Δ S := Derivation.hypothesis List.mem_cons_self
  have a := Derivation.conjunctionRight h
  have b := Derivation.conjunctionRight a
  have c := Derivation.conjunctionRight b
  have d := Derivation.conjunctionRight c
  obtain ⟨result⟩ := exact_OpenProjectedCountNil B (α ⊕ Fin 6) Δ (pool.relabel j)
    fl fr p pl pr joined ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionLeft a⟩
    ⟨Derivation.conjunctionLeft b⟩ ⟨Derivation.conjunctionLeft c⟩
    ⟨Derivation.conjunctionLeft d⟩ ⟨Derivation.conjunctionRight d⟩
  exact ⟨Derivation.implicationIntroduction result⟩

private theorem consAt (code row tail pool : OTerm α)
    (cell : D B Γ (consGraph code row tail)) (ih : D B Γ (atRows tail pool)) :
    D B Γ (atRows code pool) := by
  apply actualFiniteUniversalIntroduction B α 6 Γ (matrix code pool)
  let j : α → α ⊕ Fin 6 := Sum.inl
  let G := Γ.map (fun p => p.relabel j)
  let fl : OTerm (α ⊕ Fin 6) := .var (.inr 0)
  let fr : OTerm (α ⊕ Fin 6) := .var (.inr 1)
  let p : OTerm (α ⊕ Fin 6) := .var (.inr 2)
  let pl : OTerm (α ⊕ Fin 6) := .var (.inr 3)
  let pr : OTerm (α ⊕ Fin 6) := .var (.inr 4)
  let joined : OTerm (α ⊕ Fin 6) := .var (.inr 5)
  let n := code.relabel j
  let h := row.relabel j
  let t := tail.relabel j
  let po := pool.relabel j
  let S := reportMatrix n po fl fr p pl pr joined
  let Δ := S :: G
  change D B G (S.imp (compared p joined))
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ :=
    fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have cell' := renameInto cell j Δ keep
  rw [consGraphRename] at cell'
  have ih' := renameInto ih j Δ keep
  rw [atRowsRename] at ih'
  obtain ⟨result⟩ := exact_OpenProjectedCountInductionCons exact_ProjectedCountOnLeft
    exact_ProjectedCountOnRight B (α ⊕ Fin 6) Δ n h t po fl fr p pl pr joined cell' ih'
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction result⟩

private theorem constructorsAt (pool : OTerm α) :
    D B Γ (constructors (motive pool)) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (motive pool))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let G := Γ.map (fun p => p.relabel j)
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let po := pool.relabel j
  let R := atRows t po
  let Δ := R :: C :: G
  change D B G (C.imp ((atIndex (motive pool) 2).imp (atIndex (motive pool) 0)))
  simp only [motiveAtIndex]
  obtain ⟨out⟩ := consAt (B := B) (Γ := Δ) n h t po
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

/-- Complete original object induction for projected count recombination
on arbitrary original input and actual successful output reports. -/
theorem exact_OpenProjectedCount : ExactOpenProjectedCount := by
  intro B α Γ code pool fl fr p pl pr joined report
  have base : D B Γ (atCode (motive pool) z) := by
    rw [motiveAtCode]
    exact nilAt pool
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := constructorsAt (B := B) (Γ := Γ) pool
  have package : D B Γ (premises (motive pool)) :=
    ⟨Derivation.conjunctionIntroduction base step⟩
  have out := actualOriginalListInductionAtCode B α Γ (motive pool) code package
  rw [motiveAtCode] at out
  exact applyAtRows code pool fl fr p pl pr joined out report

#print axioms exact_OpenProjectedCount

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionProof
