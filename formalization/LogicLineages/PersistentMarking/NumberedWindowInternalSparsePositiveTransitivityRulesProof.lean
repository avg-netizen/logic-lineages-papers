module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityMotiveProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityNilProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityGapProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityConsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityGapProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityRulesProof
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
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt)
open NumberedWindowInternalSparsePositiveTerminalityGapProof (gapRename)
open NumberedWindowInternalSparsePositiveTransitivityTargets
open NumberedWindowInternalSparsePositiveTransitivityBindingProof (uniformRename)
open NumberedWindowInternalSparsePositiveTransitivityMotiveProof
open NumberedWindowInternalSparsePositiveTransitivityNilProof (fromNil)
open NumberedWindowInternalSparsePositiveTransitivityGapProof (badFinish)
open NumberedWindowInternalSparsePositiveTransitivityConsProof (fromCons)

private theorem nilRule (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (atCode (motive raw least ctx ty) z)) := by
  rw [motiveAt]
  apply introUniform raw least ctx ty z
  intro Δ _ first last
  change Nonempty (Derivation body Δ (finishAt raw least (rowLift ctx) (rowLift ty) rowSrc
    (z.relabel Sum.inl) rowMid)) at first
  rw [zRelabel] at first
  exact fromNil raw least (rowLift ctx) (rowLift ty) rowSrc rowMid rowSecond rowDst first last

private theorem gapUniform {body : Positive (Fin 1)} (raw : Program 5) (least : Program 3)
    {α : Type} {Γ : List (Formula α)} (ctx ty code : OTerm α)
    (gap : Nonempty (Derivation body Γ (malformed code))) :
    Nonempty (Derivation body Γ (uniformAt raw least ctx ty code)) := by
  apply introUniform raw least ctx ty code
  intro Δ hJ first _
  have d := renameInto gap Sum.inl Δ hJ
  rw [gapRename] at d
  exact badFinish raw least (rowLift ctx) (rowLift ty) rowSrc (rowLift code) rowMid _ d first

private theorem gapCase (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (gapRule (motive raw least ctx ty))) := by
  let code : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let bad := malformed code
  obtain ⟨row⟩ := gapUniform (body := body) (Γ := [bad]) raw least (ctx.relabel Sum.inl)
    (ty.relabel Sum.inl) code ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction row)⟩

private theorem consUniform {body : Positive (Fin 1)} (raw : Program 5) (least : Program 3)
    {α : Type} {Γ : List (Formula α)} (ctx ty code head tail : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code head tail)))
    (ih : Nonempty (Derivation body Γ (uniformAt raw least ctx ty tail))) :
    Nonempty (Derivation body Γ (uniformAt raw least ctx ty code)) := by
  apply introUniform raw least ctx ty code
  intro Δ hJ first last
  have c := renameInto cell Sum.inl Δ hJ
  rw [consGraphRename] at c
  have h := renameInto ih Sum.inl Δ hJ
  rw [uniformRename] at h
  exact fromCons raw least (rowLift ctx) (rowLift ty) rowSrc (rowLift code) (rowLift head) (rowLift tail)
    rowMid rowSecond rowDst c first last h

private theorem consCase (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (consRule (motive raw least ctx ty))) := by
  unfold consRule
  apply actualFiniteUniversalIntroduction body α 3 [] (consBody (motive raw least ctx ty))
  unfold consBody
  rw [motiveIndex,motiveIndex]
  let code : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let head : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tail : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let p := consGraph code head tail
  let q := uniformAt raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl) tail
  have c : Derivation body [q,p] p := Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d⟩ := consUniform (Γ := [q,p]) raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl) code head tail
    ⟨c⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem motivePremises (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (premises (motive raw least ctx ty))) := by
  obtain ⟨nil⟩ := nilRule body raw least ctx ty
  obtain ⟨gap⟩ := gapCase body raw least ctx ty
  obtain ⟨cons⟩ := consCase body raw least ctx ty
  exact ⟨Derivation.conjunctionIntroduction nil (Derivation.conjunctionIntroduction gap cons)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityRulesProof
