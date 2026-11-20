module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityMotiveProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityGapProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityConsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityRulesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseFieldInductionTargets
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePositiveTerminalityTargets
open NumberedWindowInternalSparsePositiveTerminalityUniformBindingProof (uniformRename)
open NumberedWindowInternalSparsePositiveTerminalityMotiveProof
open NumberedWindowInternalSparsePositiveTerminalityGapProof (gapRename fromGap)
open NumberedWindowInternalSparsePositiveTerminalityNilProof (fromNil)
open NumberedWindowInternalSparsePositiveTerminalityConsProof (fromCons)

private theorem nilRule (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (atCode (motive raw least ctx ty) z)) := by
  rw [motiveAt]
  apply introUniform raw least ctx ty z
  intro Δ _ _ loop
  change Nonempty (Derivation body Δ (loopGraph raw least rowOut rowFuel
    (rowLift ctx) (rowLift ty) rowCurrent (z.relabel Sum.inl))) at loop
  rw [zRelabel] at loop
  exact fromNil raw least rowOut rowFuel (rowLift ctx) (rowLift ty) rowCurrent loop

private theorem gapUniform {body : Positive (Fin 1)} (raw : Program 5) (least : Program 3)
    {α : Type} {Γ : List (Formula α)} (ctx ty cert : OTerm α)
    (bad : Nonempty (Derivation body Γ (malformed cert))) :
    Nonempty (Derivation body Γ (uniformAt raw least ctx ty cert)) := by
  apply introUniform raw least ctx ty cert
  intro Δ hJ bound loop
  have h := renameInto bad Sum.inl Δ hJ
  rw [gapRename] at h
  exact fromGap raw least rowOut rowFuel (rowLift ctx) (rowLift ty) rowCurrent (rowLift cert) bound loop h

private theorem gapCase (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (gapRule (motive raw least ctx ty))) := by
  let cert : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let bad := malformed cert
  obtain ⟨row⟩ := gapUniform (body := body) (Γ := [bad]) raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl)
    cert ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction row)⟩

private theorem consUniform {body : Positive (Fin 1)} (raw : Program 5) (least : Program 3)
    {α : Type} {Γ : List (Formula α)} (ctx ty cert hd tl : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (ih : Nonempty (Derivation body Γ (uniformAt raw least ctx ty tl))) :
    Nonempty (Derivation body Γ (uniformAt raw least ctx ty cert)) := by
  apply introUniform raw least ctx ty cert
  intro Δ hJ bound loop
  have h := renameInto cell Sum.inl Δ hJ
  rw [consGraphRename] at h
  have i := renameInto ih Sum.inl Δ hJ
  rw [uniformRename] at i
  exact fromCons raw least rowOut rowFuel (rowLift ctx) (rowLift ty) rowCurrent (rowLift cert)
    (rowLift hd) (rowLift tl) bound loop h i

private theorem consCase (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (consRule (motive raw least ctx ty))) := by
  unfold consRule
  apply actualFiniteUniversalIntroduction body α 3 [] (consBody (motive raw least ctx ty))
  unfold consBody
  rw [motiveIndex,motiveIndex]
  let cert : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let hd : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tl : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let p := consGraph cert hd tl
  let q := uniformAt raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl) tl
  have cell : Derivation body [q,p] p := Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨h⟩ := consUniform (Γ := [q,p]) raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl)
    cert hd tl ⟨cell⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

theorem motivePremises (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (premises (motive raw least ctx ty))) := by
  obtain ⟨nil⟩ := nilRule body raw least ctx ty
  obtain ⟨gap⟩ := gapCase body raw least ctx ty
  obtain ⟨cons⟩ := consCase body raw least ctx ty
  exact ⟨Derivation.conjunctionIntroduction nil (Derivation.conjunctionIntroduction gap cons)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityRulesProof
