module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOrigin
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListInduction
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalDirectTargetMapOriginTargets
open NumberedWindowInternalDirectTargetMapOriginSyntaxProof
open NumberedWindowInternalDirectTargetMapOriginStepProof (nilAt consAt useAtOutput)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

attribute [local irreducible] atOutput

private theorem closeAll (code key : OTerm α)
    (held : Nonempty (Derivation B (Γ.map weaken) (allOutputsBody code key))) :
    Nonempty (Derivation B Γ (allOutputs code key)) := by
  unfold allOutputs
  obtain ⟨d⟩ := held
  exact ⟨Derivation.universalIntroduction d⟩

private theorem nilBody (key : OTerm α) :
    Nonempty (Derivation B (Γ.map weaken) (allOutputsBody z key)) := by
  have zeroWeaken : (z : OTerm α).relabel (Sum.inl : α → α ⊕ Fin 1) = z :=
    zRelabel Sum.inl
  rw [allOutputsBody,zeroWeaken]
  exact nilAt (key.relabel Sum.inl) (.var (.inr 0))

private theorem nilAll (key : OTerm α) :
    Nonempty (Derivation B Γ (allOutputs z key)) :=
  closeAll z key (nilBody key)

private theorem consAll (code row tail key : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code row tail)))
    (ih : Nonempty (Derivation B Γ (allOutputs tail key))) :
    Nonempty (Derivation B Γ (allOutputs code key)) := by
  let ρ : α → α ⊕ Fin 1 := Sum.inl
  let Δ := Γ.map (fun f => f.relabel ρ)
  have keep : ∀ f ∈ Γ, f.relabel ρ ∈ Δ := by
    intro f h
    exact List.mem_map.mpr ⟨f,h,rfl⟩
  have c' := renameInto cell ρ Δ keep
  rw [consGraphRename] at c'
  have i' := renameInto ih ρ Δ keep
  rw [allOutputsRename] at i'
  have held : Nonempty (Derivation B Δ (allOutputsBody code key)) :=
    consAt (code.relabel ρ) (row.relabel ρ) (tail.relabel ρ) (key.relabel ρ) (.var (.inr 0)) c' i'
  obtain ⟨d⟩ := held
  exact ⟨Derivation.universalIntroduction d⟩

private theorem constructorLaw (key : OTerm α) :
    Nonempty (Derivation B Γ (constructors (motive key))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (motive key))
  let ρ : α → α ⊕ Fin 3 := Sum.inl
  let code : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let row : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tail : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph code row tail
  let R := allOutputs tail (key.relabel ρ)
  let Δ := R :: C :: Γ.map (fun f => f.relabel ρ)
  change Nonempty (Derivation B (Γ.map (fun f => f.relabel ρ))
    (C.imp ((atIndex (motive key) 2).imp (atIndex (motive key) 0))))
  simp only [motiveIndex]
  obtain ⟨out⟩ := consAll (B := B) (Γ := Δ)
    code row tail (key.relabel ρ)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

theorem exactOpenProjectedTargetOrigin : ExactOpenProjectedTargetOrigin := by
  intro B α Γ code output key
  have base : Nonempty (Derivation B Γ (atCode (motive key) z)) := by
    rw [motiveCode]
    exact nilAll key
  obtain ⟨start⟩ := base
  obtain ⟨step⟩ := constructorLaw (B := B) (Γ := Γ) key
  have checked : Nonempty (Derivation B Γ (premises (motive key))) :=
    ⟨Derivation.conjunctionIntroduction start step⟩
  have all := actualOriginalListInductionAtCode B α Γ (motive key) code checked
  rw [motiveCode] at all
  exact useAtOutput code key output all

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOrigin
