module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafShapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualAddressedAllAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedBetaInstanceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof (fieldsRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralBetaLeafProof (withBetaLeaf)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralBetaLeafShapeProof (exact_OpenInstalledBetaLeafShape)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Read the genuine beta destination via the same raw-instance
program that the leaf invokes, and preserve its selected output code
in the original target-address report. Neither input nor destination
is replaced by a newly computed address. -/
theorem exact_OpenAddressedBetaInstance (V : Program 1) (U : Program 2) (leaf : Nat → Program 3)
    (R : Program 5) (L : Program 3) (y ctx ty before after cert q w r payload : OTerm α)
    (goal : Formula α)
    (target : D B Γ (addressReport y ctx ty after))
    (actual : D B Γ (hopCalls R L ctx ty before cert after q w r))
    (branch : D B Γ (bit (withBetaLeaf V U leaf 6) ![q,payload,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (dom cod f a bind body : OTerm β), (∀ e ∈ Γ, e.relabel j ∈ Δ) →
      D B Δ (eqn (q.relabel j) (auxiliaryTerm dom cod f a)) →
      D B Δ (eqn f (rawLambdaTerm bind body)) → D B Δ (eqn dom bind) →
      D B Δ (programGraph U (suc (r.relabel j)) ![a,body]) →
      D B Δ (programGraph L (suc (before.relabel j)) ![ctx.relabel j,ty.relabel j,q.relabel j]) →
      D B Δ (programGraph L (suc (after.relabel j)) ![ctx.relabel j,ty.relabel j,r.relabel j]) →
      D B Δ (addressReport (y.relabel j) (ctx.relabel j) (ty.relabel j) (after.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply exact_OpenInstalledBetaLeafShape V U leaf q payload r goal branch
  intro β j Δ dom cod f a bind body keep parsed head same ran
  have addressed := renameInto target j Δ keep
  rw [addressReportRename] at addressed
  have checked := renameInto actual j Δ keep
  rw [fieldsRename] at checked
  obtain ⟨row⟩ := checked
  let values := Derivation.conjunctionRight (Derivation.conjunctionRight row)
  exact use β j Δ dom cod f a bind body keep parsed head same ran
    ⟨Derivation.conjunctionLeft values⟩ ⟨Derivation.conjunctionRight values⟩ addressed

#print axioms exact_OpenAddressedBetaInstance
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedBetaInstanceProof
