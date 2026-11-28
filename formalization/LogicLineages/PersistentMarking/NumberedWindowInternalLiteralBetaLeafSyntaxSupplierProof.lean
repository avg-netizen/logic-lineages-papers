module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenParentProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafSyntaxSupplierProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue headTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverAuxSyntaxOpenParentProof (exact_OpenCoverAuxSyntaxParent)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralBetaLeafProof (literalBetaLeaf)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The two syntax conjuncts of an accepted beta leaf, which the beta
call record does not retain: the leaf's own syntax program accepts the
source redex and the target. -/
theorem exact_OpenLiteralBetaLeafSyntax (V : Program 1) (U : Program 2) (q w r : OTerm α)
    (held : D B Γ (bit (literalBetaLeaf V U) ![q,w,r])) :
    D B Γ (unary V (suc z) q) ∧ D B Γ (unary V (suc z) r) := by
  unfold literalBetaLeaf at held
  let xs : Fin 3 → OTerm α := ![q,w,r]
  obtain ⟨a⟩ := conjunctionRecover _ _ xs held
  obtain ⟨b⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight a⟩
  have source : D B Γ (unary V (suc z) q) := by
    apply compositionRecover V (fun _ : Fin 1 => .projection (0 : Fin 3)) (suc z) xs ![q]
      ⟨Derivation.conjunctionLeft a⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (0 : Fin 3) xs
  have target : D B Γ (unary V (suc z) r) := by
    apply compositionRecover V (fun _ : Fin 1 => .projection (2 : Fin 3)) (suc z) xs ![r]
      ⟨Derivation.conjunctionLeft b⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue (2 : Fin 3) xs
  exact ⟨source,target⟩

/-- Auxiliary descent for the installed unit syntax program: acceptance
of a code that is derivably a literal auxiliary application gives both
type bits and the same program's acceptance of the function and the
argument. This is the existing parent theorem between the two
normalization steps. -/
theorem exact_OpenUnitAuxSyntaxOperands (V TV : Program 1) (q dom cod fn arg : OTerm α)
    (source : D B Γ (eqn q (auxiliaryTerm dom cod fn arg)))
    (valid : D B Γ (unary (unitAuxSyntax V TV) (suc z) q)) :
    D B Γ (unary TV (suc z) dom) ∧ D B Γ (unary TV (suc z) cod) ∧
    D B Γ (unary (unitAuxSyntax V TV) (suc z) fn) ∧
    D B Γ (unary (unitAuxSyntax V TV) (suc z) arg) := by
  have moved : D B Γ (unary (unitAuxSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)) :=
    headTransport (unitAuxSyntax V TV) (suc z) q (auxiliaryTerm dom cod fn arg) Fin.elim0
      source valid
  have raw := normalizeRecover (auxSyntax V TV) ![auxiliaryTerm dom cod fn arg] moved
  obtain ⟨children⟩ := exact_OpenCoverAuxSyntaxParent V TV B α Γ dom cod fn arg raw
  have types := Derivation.conjunctionLeft children
  have terms := Derivation.conjunctionRight children
  exact ⟨⟨Derivation.conjunctionLeft types⟩,⟨Derivation.conjunctionRight types⟩,
    normalizeAccept (auxSyntax V TV) ![fn] ⟨Derivation.conjunctionLeft terms⟩,
    normalizeAccept (auxSyntax V TV) ![arg] ⟨Derivation.conjunctionRight terms⟩⟩

/-- Supplier for the `inserted` premise. With the leaf graph and the two
row equations `source` and `functionShape`, the installed syntax program
accepts the beta argument, the literal function lambda node, and the
target. Nothing is concluded about the lambda's body. -/
theorem exact_OpenBetaLeafArgumentSyntax (V TV : Program 1) (U : Program 2)
    (q w r dom cod fn arg bind body : OTerm α)
    (leaf : D B Γ (bit (literalBetaLeaf (unitAuxSyntax V TV) U) ![q,w,r]))
    (source : D B Γ (eqn q (auxiliaryTerm dom cod fn arg)))
    (functionShape : D B Γ (eqn fn (rawLambdaTerm bind body))) :
    D B Γ (unary (unitAuxSyntax V TV) (suc z) arg) ∧
    D B Γ (unary (unitAuxSyntax V TV) (suc z) (rawLambdaTerm bind body)) ∧
    D B Γ (unary (unitAuxSyntax V TV) (suc z) r) := by
  obtain ⟨valid,target⟩ := exact_OpenLiteralBetaLeafSyntax (unitAuxSyntax V TV) U q w r leaf
  obtain ⟨_,_,fnValid,argValid⟩ :=
    exact_OpenUnitAuxSyntaxOperands V TV q dom cod fn arg source valid
  exact ⟨argValid,
    headTransport (unitAuxSyntax V TV) (suc z) fn (rawLambdaTerm bind body) Fin.elim0
      functionShape fnValid,
    target⟩

#print axioms exact_OpenLiteralBetaLeafSyntax
#print axioms exact_OpenUnitAuxSyntaxOperands
#print axioms exact_OpenBetaLeafArgumentSyntax
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafSyntaxSupplierProof
