module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalOriginRowsFilterTargets (rowCell)
open NumberedWindowInternalOriginScanInductionSyntaxProof
  (atRowsRename motiveAtCode motiveAtIndex applyAtRows renamePools)
open NumberedWindowInternalOriginScanInductionConsProof (exact_OpenOriginScanInductionCons)
open NumberedWindowInternalOriginScanNilProof (exact_OpenOriginScanNil)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalOriginScanInductionTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilAt (r : Program 3) (removed rawL rawR scratchL : OTerm α) :
    D B Γ (atRows r z removed rawL rawR scratchL) := by
  apply actualFiniteUniversalIntroduction B α 2 Γ (matrix r z removed rawL rawR scratchL)
  let j : α → α ⊕ Fin 2 := Sum.inl
  let G := Γ.map (fun p => p.relabel j)
  let u : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let v : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let S := loopAccept r z (removed.relabel j) ⊓
    (filterGraph true u z (scratchL.relabel j) ⊓ filterGraph false v z (scratchL.relabel j))
  let goal := goalAt r (rawL.relabel j) (rawR.relabel j) u v
  change D B G (suppliedAt r (z.relabel j) (removed.relabel j)
    (rawL.relabel j) (rawR.relabel j) (scratchL.relabel j) u v)
  rw [zRelabel]
  change D B G (S.imp goal)
  have h : Derivation B (S :: G) S := Derivation.hypothesis List.mem_cons_self
  have both := Derivation.conjunctionRight h
  obtain ⟨l⟩ := exact_OpenOriginScanNil true r B (α ⊕ Fin 2) (S :: G)
    u (scratchL.relabel j) (rawL.relabel j) ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨r'⟩ := exact_OpenOriginScanNil false r B (α ⊕ Fin 2) (S :: G)
    v (scratchL.relabel j) (rawR.relabel j) ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction l r')⟩

private theorem consAt (r : Program 3)
    (code head tail removed decoded rawL rawR scratchL scratchR joined : OTerm α)
    (pool : Pools B Γ removed decoded rawL rawR scratchL scratchR joined)
    (cell : D B Γ (consGraph code head tail))
    (inherited : D B Γ (atRows r tail removed rawL rawR scratchL)) :
    D B Γ (atRows r code removed rawL rawR scratchL) := by
  apply actualFiniteUniversalIntroduction B α 2 Γ (matrix r code removed rawL rawR scratchL)
  let j : α → α ⊕ Fin 2 := Sum.inl
  let G := Γ.map (fun p => p.relabel j)
  let u : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let v : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let co := code.relabel j
  let hr := head.relabel j
  let tr := tail.relabel j
  let old := removed.relabel j
  let oldScratch := decoded.relabel j
  let l := rawL.relabel j
  let rr := rawR.relabel j
  let sl := scratchL.relabel j
  let sr := scratchR.relabel j
  let app := joined.relabel j
  let S := loopAccept r co old ⊓ (filterGraph true u co sl ⊓ filterGraph false v co sl)
  let goal := goalAt r l rr u v
  change D B G (S.imp goal)
  let Δ := S :: G
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ :=
    fun p pp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,pp,rfl⟩)
  have p' := renamePools pool j keep
  have cell' := renameInto cell j Δ keep
  rw [consGraphRename] at cell'
  have law' := renameInto inherited j Δ keep
  rw [atRowsRename] at law'
  have h : Derivation B Δ S := Derivation.hypothesis List.mem_cons_self
  have both := Derivation.conjunctionRight h
  obtain ⟨got⟩ := exact_OpenOriginScanInductionCons r B (α ⊕ Fin 2) Δ
    co hr tr old oldScratch l rr sl sr app u v p' cell' law'
    ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.implicationIntroduction got⟩

private theorem constructorsAt (r : Program 3)
    (removed decoded rawL rawR scratchL scratchR joined : OTerm α)
    (pool : Pools B Γ removed decoded rawL rawR scratchL scratchR joined) :
    D B Γ (constructors (motive r removed rawL rawR scratchL)) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (motive r removed rawL rawR scratchL))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let co : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let hr : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tr : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let G := Γ.map (fun p => p.relabel j)
  let C := consGraph co hr tr
  let old := removed.relabel j
  let l := rawL.relabel j
  let rr := rawR.relabel j
  let sl := scratchL.relabel j
  let I := atRows r tr old l rr sl
  let Δ := I :: C :: G
  change D B G (C.imp ((atIndex (motive r removed rawL rawR scratchL) 2).imp
    (atIndex (motive r removed rawL rawR scratchL) 0)))
  simp only [motiveAtIndex]
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ :=
    fun p pp => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,pp,rfl⟩))
  have p' := renamePools pool j keep
  obtain ⟨out⟩ := consAt (B := B) (Γ := Δ) r co hr tr old (decoded.relabel j) l rr sl
    (scratchR.relabel j) (joined.relabel j) p'
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

/-- Original object-list induction for the simultaneous certified scan
property on the two actual complementary filters, at any symbolic input. -/
theorem exact_OpenOriginScanAtRows : ExactOpenOriginScanAtRows := by
  intro r B α Γ rows removed decoded rawL rawR scratchL scratchR joined outL outR
    pool original filterL filterR
  have base : D B Γ (atCode (motive r removed rawL rawR scratchL) z) := by
    rw [motiveAtCode]
    exact nilAt r removed rawL rawR scratchL
  obtain ⟨b⟩ := base
  obtain ⟨s⟩ := constructorsAt r removed decoded rawL rawR scratchL scratchR joined pool
  have evidence : D B Γ (premises (motive r removed rawL rawR scratchL)) :=
    ⟨Derivation.conjunctionIntroduction b s⟩
  have ind := actualOriginalListInductionAtCode B α Γ (motive r removed rawL rawR scratchL) rows evidence
  rw [motiveAtCode] at ind
  exact applyAtRows r rows removed rawL rawR scratchL outL outR ind original filterL filterR

#print axioms exact_OpenOriginScanAtRows

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionProof
