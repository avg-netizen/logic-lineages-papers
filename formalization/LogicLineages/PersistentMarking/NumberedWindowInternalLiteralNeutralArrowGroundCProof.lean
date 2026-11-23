module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralGroundEndpointProof
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralArrowGroundCProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph (equal)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqnRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm freeTerm bottomTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm consTerm)
open NumberedWindowInternalApplicationOutputGuardTargets (outputGuard)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof (literalNeutral exact_OpenLiteralNeutralBottomAuxI)
open NumberedWindowInternalLiteralNeutralGroundEndpointProof
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename moveFree moveBottom)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalAuxBottomRefinementObjectTargets (packedAuxBottomTerm)
open NumberedWindowComputabilityFormulaTargets (accepts formula)
open NumberedWindowTypeApplicationRuleChecks (exact_ApplicationIntroduction)

private theorem consRename {α β : Type} (x y : OTerm α) (j : α → β) :
    (consTerm x y).relabel j = consTerm (x.relabel j) (y.relabel j) :=
  rawConsRename x y j

private theorem freeHeadRename {α β : Type} (t n : OTerm α) (j : α → β) :
    (freeTerm t n).relabel j = freeTerm (t.relabel j) (n.relabel j) := by
  simp only [freeTerm,consRename,zRelabel]

private theorem bottomHeadRename {α β : Type} (t : OTerm α) (j : α → β) :
    (bottomTerm t).relabel j = bottomTerm (t.relabel j) := by
  simp only [bottomTerm,consRename,numeralRename,zRelabel]

/-- A same-body source interface requiring only I at a genuine carried
free-headed auxiliary. Not a new computability or typing assumption. -/
@[expose] def FreeAuxiliaryI (i : Program 1) (r : Program 3) (c : Nat) : Prop :=
  ∀ (β : Type) (Δ : List (Formula β)) (y ctx dom cod stored name arg : OTerm β),
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Δ
      (equal y (auxAddressTerm ctx dom cod (freeTerm stored name) arg))) →
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Δ
      (carrier (literalNeutral i r) false c y)) →
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Δ (membership false y))

/-- The literal arrow introduction used below. The actual domain C
assumption is retained in the context even though auxiliary endpoint I
does not need it. -/
private theorem introduce {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (P : Program 3) (σ : ProbeTy) (f : OTerm α)
    (step : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (u y : OTerm β),
      (∀ g ∈ Γ, g.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (accepts P (f.relabel j) u y)) →
      Nonempty (Derivation B Δ (membership false y))) :
    Nonempty (Derivation B Γ (formula P (.arrow σ .ground) f)) := by
  apply exact_ApplicationIntroduction B P σ .ground α Γ f
  let β := (α ⊕ Fin 1) ⊕ Fin 1
  let j : α → β := fun x => .inl (.inl x)
  let u : OTerm β := .var (.inl (.inr 0))
  let y : OTerm β := .var (.inr 0)
  let a := formula P σ u
  let b := accepts P (f.relabel j) u y
  let Δ := a :: b :: (Γ.map weaken).map weaken
  change Nonempty (Derivation B Δ (membership false y))
  apply step β j Δ u y
  · intro g hg
    apply List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    refine List.mem_map.mpr ⟨g.relabel Sum.inl,List.mem_map.mpr ⟨g,hg,rfl⟩,?_⟩
    exact ID1Completion.InternalPositiveUnfoldingSupportProof.formulaRelabelComposition
      (Sum.inl : α → α ⊕ Fin 1) (Sum.inl : α ⊕ Fin 1 → β) g
  · exact ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩

variable {i : Program 1} {r p : Program 3} {c : Nat} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenLiteralNeutralFreeArrowGroundC
    (auxI : FreeAuxiliaryI i r c)
    (σ : ProbeTy) (f ctx ty name : OTerm α)
    (declared : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal ty (numeral (typeCode (.arrow σ .ground))))))
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal f (packedFreeTerm ctx ty name)))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (formula (outputGuard i (refinedApplication p)) (.arrow σ .ground) f)) := by
  let B := sourceBody (literalNeutral i r) c
  apply introduce (outputGuard i (refinedApplication p)) σ f
  intro β j Δ u y keep app
  have d : Nonempty (Derivation B Δ (equal (ty.relabel j) (numeral (typeCode (.arrow σ .ground))))) := by
    simpa only [equalEqn,eqnRelabel,numeralRename] using renameInto declared j Δ keep
  have h := moveFree f ctx ty name j keep shape
  apply exact_OpenLiteralNeutralFreeGroundEndpoint σ (f.relabel j) (ctx.relabel j)
    (ty.relabel j) (name.relabel j) u y (membership false y) d h app
  intro γ k Θ dom cod a a' _ fields carried
  rw [membershipRename]
  apply auxI γ Θ (y.relabel k) ((ctx.relabel j).relabel k) dom cod
    ((ty.relabel j).relabel k) ((name.relabel j).relabel k) a' _ carried
  simpa only [freeHeadRename] using fields.endpoint

theorem exact_OpenLiteralNeutralBottomArrowGroundC
    (σ : ProbeTy) (f ctx ty : OTerm α)
    (declared : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal ty (numeral (typeCode (.arrow σ .ground))))))
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal f (packedBottomTerm ctx ty)))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (formula (outputGuard i (refinedApplication p)) (.arrow σ .ground) f)) := by
  let B := sourceBody (literalNeutral i r) c
  apply introduce (outputGuard i (refinedApplication p)) σ f
  intro β j Δ u y keep app
  have d : Nonempty (Derivation B Δ (equal (ty.relabel j) (numeral (typeCode (.arrow σ .ground))))) := by
    simpa only [equalEqn,eqnRelabel,numeralRename] using renameInto declared j Δ keep
  have h := moveBottom f ctx ty j keep shape
  apply exact_OpenLiteralNeutralBottomGroundEndpoint σ (f.relabel j) (ctx.relabel j)
    (ty.relabel j) u y (membership false y) d h app
  intro γ k Θ dom cod a a' _ fields carried
  rw [membershipRename]
  apply exact_OpenLiteralNeutralBottomAuxI i r c γ Θ (y.relabel k)
    ((ctx.relabel j).relabel k) dom cod ((ty.relabel j).relabel k) a' _ carried
  simpa only [packedAuxBottomTerm,bottomHeadRename] using fields.endpoint

#print axioms exact_OpenLiteralNeutralFreeArrowGroundC
#print axioms exact_OpenLiteralNeutralBottomArrowGroundC
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralArrowGroundCProof
