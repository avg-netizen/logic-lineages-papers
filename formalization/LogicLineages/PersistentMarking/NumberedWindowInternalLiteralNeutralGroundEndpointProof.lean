module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalTypedNeutralEndpointCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralGroundEndpointProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph (equal)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets
  (literalApplicationShape auxAddressTerm freeTerm bottomTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalAtomicApplicationShapeObjectChecks (exact_OpenAtomicApplicationShape)
open NumberedWindowInternalApplicationOutputGuardTargets (outputGuard)
open NumberedWindowInternalApplicationOutputGuardOpenProof (exact_OpenApplicationOutputGuard)
open NumberedWindowInternalTypedNeutralEndpointCasesProof (EndpointReports exact_OpenTypedNeutralEndpointCases)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral neutralWithCarrier)
open NumberedWindowInternalAuxBottomMembership (augmented)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowComputabilityFormulaTargets (accepts)

variable {i : Program 1} {r p : Program 3} {c : Nat} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenLiteralNeutralApplicationCarrier
    (f u y : OTerm α)
    (app : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (accepts (outputGuard i (refinedApplication p)) f u y))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (accepts (refinedApplication p) f u y)) ∧
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (carrier (literalNeutral i r) false c y)) := by
  let R := augmented i (neutralWithCarrier i r)
  let B := sourceBody (literalNeutral i r) c
  obtain ⟨shaped,check⟩ := exact_OpenApplicationOutputGuard i (refinedApplication p) B α Γ f u y app
  exact ⟨shaped,(exact_DomainRules i (jRaw i) R (dCore i R permutation)
    false c B α Γ y).2 check⟩

/-- A typed endpoint continuation on the real four bound fields, plus the
scalar carrier derived from the same accepted physical call. -/
@[expose] def GroundEndpointContinuation (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} (Γ : List (Formula α)) (σ : ProbeTy)
    (ctx head arg out : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (dom cod a a' : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    EndpointReports (sourceBody (literalNeutral i r) c) Δ σ .ground
      (ctx.relabel j) (head.relabel j) (arg.relabel j) (out.relabel j) dom cod a a' →
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Δ
      (carrier (literalNeutral i r) false c (out.relabel j))) →
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Δ (goal.relabel j))

private theorem typedEndpoint
    (σ : ProbeTy) (ctx ty head arg out : OTerm α) (goal : Formula α)
    (declared : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal ty (numeral (typeCode (.arrow σ .ground))))))
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (literalApplicationShape ctx ty head arg out)))
    (held : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (carrier (literalNeutral i r) false c out)))
    (next : GroundEndpointContinuation i r c Γ σ ctx head arg out goal) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ goal) := by
  apply exact_OpenTypedNeutralEndpointCases σ .ground ctx ty head arg out declared shape goal
  intro β j Δ dom cod a a' keep fields
  have carried := renameInto held j Δ keep
  rw [NumberedWindowInternalFreshProbeAlignmentSyntaxProof.carrierRename] at carried
  exact next β j Δ dom cod a a' keep fields carried

theorem exact_OpenLiteralNeutralFreeGroundEndpoint
    (σ : ProbeTy) (f ctx ty name u y : OTerm α) (goal : Formula α)
    (declared : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal ty (numeral (typeCode (.arrow σ .ground))))))
    (free : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (equal f (packedFreeTerm ctx ty name))))
    (app : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (accepts (outputGuard i (refinedApplication p)) f u y)))
    (next : GroundEndpointContinuation i r c Γ σ ctx (freeTerm ty name) u y goal) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ goal) := by
  obtain ⟨shaped,carried⟩ := exact_OpenLiteralNeutralApplicationCarrier f u y app
  have output := exact_OpenAtomicApplicationShape.1 p _ α Γ f u y ctx ty name free shaped
  exact typedEndpoint σ ctx ty (freeTerm ty name) u y goal declared output carried next

theorem exact_OpenLiteralNeutralBottomGroundEndpoint
    (σ : ProbeTy) (f ctx ty u y : OTerm α) (goal : Formula α)
    (declared : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal ty (numeral (typeCode (.arrow σ .ground))))))
    (bottom : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (equal f (packedBottomTerm ctx ty))))
    (app : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (accepts (outputGuard i (refinedApplication p)) f u y)))
    (next : GroundEndpointContinuation i r c Γ σ ctx (bottomTerm ty) u y goal) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ goal) := by
  obtain ⟨shaped,carried⟩ := exact_OpenLiteralNeutralApplicationCarrier f u y app
  have output := exact_OpenAtomicApplicationShape.2 p _ α Γ f u y ctx ty bottom shaped
  exact typedEndpoint σ ctx ty (bottomTerm ty) u y goal declared output carried next

#print axioms exact_OpenLiteralNeutralApplicationCarrier
#print axioms exact_OpenLiteralNeutralFreeGroundEndpoint
#print axioms exact_OpenLiteralNeutralBottomGroundEndpoint

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralGroundEndpointProof
