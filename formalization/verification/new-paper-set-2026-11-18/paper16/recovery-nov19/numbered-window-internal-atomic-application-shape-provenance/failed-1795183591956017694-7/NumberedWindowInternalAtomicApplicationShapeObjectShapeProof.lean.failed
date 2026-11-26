module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectShapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (zeroAt)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm addressReports)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress inverseEq)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (unaryInput)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalAtomicApplicationShape NumberedWindowInternalAtomicApplicationShapeObjectTargets
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (freeChecks bottomChecks)
open NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof (shapeRename)
open NumberedWindowInternalAtomicApplicationShapeObjectTapeProof (fields fromReports)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

section
attribute [local irreducible] programGraph

private theorem reportsFromAddress (f c t k : OTerm α)
    (shape : Nonempty (Derivation B Γ (equal f (addressTerm c t k)))) :
    Nonempty (Derivation B Γ (addressReports f c t k)) := by
  let x := addressTerm c t k
  have eq := inverseEq f x shape
  obtain ⟨_,hc,ht,hk⟩ := literalAddress (body := B) (Γ := Γ) c t k
  obtain ⟨hs⟩ := unaryInput rawContext c x f eq hc
  obtain ⟨hr⟩ := unaryInput rawResult t x f eq ht
  obtain ⟨hl⟩ := unaryInput rawLeast k x f eq hk
  exact ⟨Derivation.conjunctionIntroduction hs (Derivation.conjunctionIntroduction hr hl)⟩

private theorem moveAddress {β : Type} (f c t k : OTerm α) (j : α → β)
    (Δ : List (Formula β)) (hJ : ∀ x ∈ Γ, x.relabel j ∈ Δ)
    (h : Nonempty (Derivation B Γ (addressReports f c t k))) :
    Nonempty (Derivation B Δ (addressReports (f.relabel j) (c.relabel j) (t.relabel j) (k.relabel j))) := by
  have moved := renameInto h j Δ hJ
  simpa only [addressReports,conjunctionRename,programRename,inputsRename] using moved

private theorem moveChecks {β : Type} (f u y : OTerm α) (j : α → β)
    (Δ : List (Formula β)) (hJ : ∀ x ∈ Γ, x.relabel j ∈ Δ)
    (h : Nonempty (Derivation B Γ (programGraph atomicChecks (suc z) ![f,u,y]))) :
    Nonempty (Derivation B Δ (programGraph atomicChecks (suc z) ![f.relabel j,u.relabel j,y.relabel j])) := by
  have moved := renameInto h j Δ hJ
  simpa only [programRename,tripleInputsRename,sucRelabel,zRelabel] using moved

/-- Form one genuine graph composition with a dummy constant output.
Existential elimination of its actual original graph exposes precisely
the four selected outputs in the same arithmetic context. -/
private theorem packedShape (f u y c t k : OTerm α)
    (address : Nonempty (Derivation B Γ (equal f (addressTerm c t k))))
    (checked : Nonempty (Derivation B Γ (programGraph atomicChecks (suc z) ![f,u,y]))) :
    Nonempty (Derivation B Γ (literalApplicationShape c t k u y)) := by
  let collect : Program 3 := .composition (zeroAt 4) fields
  have raw := reportsFromAddress f c t k address
  apply programCases collect ![f,u,y] (literalApplicationShape c t k u y)
  intro β j Δ out hJ main
  rw [shapeRename]
  rw [tripleInputsRename] at main
  let f₁ := f.relabel j
  let u₁ := u.relabel j
  let y₁ := y.relabel j
  let c₁ := c.relabel j
  let t₁ := t.relabel j
  let k₁ := k.relabel j
  have raw₁ : Nonempty (Derivation B Δ (addressReports f₁ c₁ t₁ k₁)) :=
    moveAddress f c t k j Δ hJ raw
  have yes₁ : Nonempty (Derivation B Δ (programGraph atomicChecks (suc z) ![f₁,u₁,y₁])) :=
    moveChecks f u y j Δ hJ checked
  change Nonempty (Derivation B Δ (literalApplicationShape c₁ t₁ k₁ u₁ y₁))
  apply programCompositionCases (zeroAt 4) fields out ![f₁,u₁,y₁]
    (literalApplicationShape c₁ t₁ k₁ u₁ y₁) main
  intro γ h vals Ξ hΞ _ reports
  rw [shapeRename]
  have final := fromReports (f₁.relabel h) (u₁.relabel h) (y₁.relabel h)
    (c₁.relabel h) (t₁.relabel h) (k₁.relabel h) vals
    (moveAddress f₁ c₁ t₁ k₁ h Ξ hΞ raw₁)
    (moveChecks f₁ u₁ y₁ h Ξ hΞ yes₁)
  apply final
  intro i
  have this := reports i
  rw [tripleInputsRename] at this
  exact this

theorem exactShape : ExactOpenAtomicApplicationShape := by
  constructor
  · intro p B α Γ f u y c t n shape accepted
    exact packedShape f u y c t (freeTerm t n) shape (freeChecks p f u y c t n shape accepted)
  · intro p B α Γ f u y c t shape accepted
    exact packedShape f u y c t (bottomTerm t) shape (bottomChecks p f u y c t shape accepted)

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectShapeProof
