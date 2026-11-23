module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointSynthesisProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedPathPrependProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedOneHopForwardProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.SourcePresentation (Data sourceBody)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalPullbackTargets (forwardImage)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (consume)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftInputs)
open NumberedWindowInternalSparseAppliedEndpointSynthesisProof (outputFromLeast acceptedFromLeast)
open NumberedWindowInternalSparseAppliedPathPrependProof (appliedHop)

private theorem acceptsGraph {α : Type} (p : Program 3) (f u y : OTerm α) :
    accepts p f u y = programGraph p (suc z) ![f,u,y] := rfl

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem edgeRename {β : Type} (S : Data) (c : Nat) (x y : OTerm α) (j : α → β) :
    (edge S false c x y).relabel j = edge S false c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge S false c x y).subst (fun a => emb (.var (j a))) = _
  rw [edgeSubst, ← termRelabelAsSubst, ← termRelabelAsSubst]

private theorem toScalar (i j : Program 1) (r d : Program 3) (c : Nat) (x y : OTerm α)
    (cert : Nonempty (Derivation body Γ (suppliedEdge r x y))) :
    Nonempty (Derivation body Γ (edge (data i j r d) false c x y)) := by
  apply consume r x y _ cert
  intro β h Δ w keep live
  rw [edgeRename]
  exact edgeIntroduction ((exact_CertificateRules i j r d false c body β Δ
    (x.relabel h) (y.relabel h) w).mpr live)

private theorem provideForward (S : Data) (p : Program 3) (c : Nat) (g u x y : OTerm α)
    (app : Nonempty (Derivation body Γ (accepts p g u y)))
    (step : Nonempty (Derivation body Γ (edge S false c x y))) :
    Nonempty (Derivation body Γ (forwardImage S p c g u x)) := by
  let row : Formula (α ⊕ Fin 1) := accepts p (g.relabel Sum.inl) (u.relabel Sum.inl) (.var (.inr 0)) ⊓
    edge S false c (x.relabel Sum.inl) (.var (.inr 0))
  have h : instantiate row (emb y) =
      (accepts p g u y ⊓ edge S false c x y) := by
    simp only [row,instantiate,bindEmbedding,conjunctionSubst,acceptsSubst,edgeSubst,liftBind,varBind]
  obtain ⟨a⟩ := app
  obtain ⟨s⟩ := step
  exact ⟨Derivation.existentialIntroduction (phi := row)
    (emb y) (h.symm ▸ Derivation.conjunctionIntroduction a s)⟩

/-- Actual one-hop image: the final y is synthesized by the physical same
least call and original address constructor. Its exact application and
original installed scalar edge are derived with a true positive certificate. -/
theorem forwardFromLeast (i j cv tv : Program 1) (d root other W least : Program 3) (V : Program 1)
    (c : Nat) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg f w g gAddr u result left k : OTerm α) :
    let raw := typedRaw5 root other W V
    let r := addressPositive cv tv raw least
    let S := data i j r d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (liftInputs root other W V ctx dom cod arg f w g)) →
    Nonempty (Derivation B Γ (unary cv (suc z) ctx)) →
    Nonempty (Derivation B Γ (unary tv (suc z) cod)) →
    Nonempty (Derivation B Γ (outputReport least ctx cod (auxiliaryTerm dom cod f arg) left)) →
    Nonempty (Derivation B Γ (unary i (suc z) gAddr)) →
    Nonempty (Derivation B Γ (unary i (suc z) u)) →
    Nonempty (Derivation B Γ (parsedApplicationInputs gAddr u ctx result dom cod g arg)) →
    Nonempty (Derivation B Γ (programGraph least (suc k) ![ctx,cod,auxiliaryTerm dom cod g arg])) →
    Nonempty (Derivation B Γ (forwardImage S (applicationGuard i least) c gAddr u left)) := by
  intro raw r S B lifted cvOK tvOK first gOK uOK parsed call
  let y := addressTerm ctx cod k
  have last := outputFromLeast least ctx cod (auxiliaryTerm dom cod g arg) k call
  have cert := appliedHop i j cv tv d root other W least V c α Γ ctx dom cod arg f w g left y
    lifted cvOK tvOK first last
  have app : Nonempty (Derivation B Γ (accepts (applicationGuard i least) gAddr u y)) := by
    rw [acceptsGraph]
    exact acceptedFromLeast i least gAddr u ctx result dom cod g arg k gOK uOK parsed call
  exact provideForward S (applicationGuard i least) c gAddr u left y app
    (toScalar i j r d c left y cert)

#print axioms forwardFromLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedOneHopForwardProof
