module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedAuxGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRefinedOpenAuxFromLeastProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalAtomicRefinement
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralRefinedAuxGuardProof (exact_OpenRefinedTagSixGuardZeros)
open NumberedWindowInternalLiteralRefinedScalarTargets (refinedLiteral)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (consume)
open NumberedWindowComputabilityFormulaTargets (accepts)

private theorem acceptsGraph {α : Type} (r : Program 3) (x w y : OTerm α) :
    accepts r x w y = programGraph r (suc z) ![x,w,y] := rfl

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem branchAST (i : Program 1) (r : Program 3) :
    refined i r =
      branch (atSource freeSource) (branch (atSource bottomSource) r (constantZero 3))
        (conjunction r (conjunction bottomTarget (atTarget i))) := by
  unfold refined
  rw [exact_DispatchControlAST.2.2.2.2.1, exact_DispatchControlAST.2.2.2.2.1,
    exact_DispatchControlAST.1, exact_DispatchControlAST.2.2.2.2.2,
    exact_DispatchControlAST.2.2.2.2.2]

private theorem applySource (p : Program 1) (x w y : OTerm α)
    (h : Nonempty (Derivation B Γ (unary p z x))) :
    Nonempty (Derivation B Γ (programGraph (atSource p) z ![x,w,y])) := by
  unfold atSource
  apply compositionValue p (fun _ : Fin 1 => .projection (0 : Fin 3)) z ![x,w,y] ![x] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue (0 : Fin 3) ![x,w,y]

/-- The actual selected least field, not the input before canonicalization,
is an auxiliary. The old positive tape then survives the refined branch. -/
theorem exact_OpenRefinedAuxLeastCertificate (i : Program 1) (r : Program 3)
    (x k w y : OTerm α)
    (read : Nonempty (Derivation B Γ (unary rawLeast k x)))
    (tag : Nonempty (Derivation B Γ (unary cellHead (numeral 6) k))) :
    Nonempty (Derivation B Γ (accepts r x w y)) ↔
      Nonempty (Derivation B Γ (accepts (refined i r) x w y)) := by
  let xs : Fin 3 → OTerm α := ![x,w,y]
  let q := branch (atSource bottomSource) r (constantZero 3)
  let yes := conjunction r (conjunction bottomTarget (atTarget i))
  have rejected := exact_OpenRefinedTagSixGuardZeros x k read tag
  have hf := applySource freeSource x w y rejected.1
  have hb := applySource bottomSource x w y rejected.2
  rw [acceptsGraph, acceptsGraph, branchAST]
  exact ⟨fun h => zeroBranchIntro (atSource freeSource) q yes (suc z) xs hf
    (zeroBranchIntro (atSource bottomSource) r (constantZero 3) (suc z) xs hb h),
    fun h => zeroBranchElim (atSource bottomSource) r (constantZero 3) (suc z) xs hb
    (zeroBranchElim (atSource freeSource) q yes (suc z) xs hf h)⟩

/-- A genuinely accepted old positive tape in the very same ambient proof
becomes an even edge in the actual literal refined body when the original
selected least field is reported at the tag-six auxiliary shape. -/
theorem exact_OpenRefinedAuxLeastEdge (i : Program 1) (r : Program 3) (c : Nat)
    (x k y : OTerm α)
    (read : Nonempty (Derivation B Γ (unary rawLeast k x)))
    (tag : Nonempty (Derivation B Γ (unary cellHead (numeral 6) k)))
    (old : Nonempty (Derivation B Γ (suppliedEdge r x y))) :
    Nonempty (Derivation B Γ (edge (refinedLiteral i r) false c x y)) := by
  apply consume r x y _ old
  intro β h Δ w keep live
  rw [edgeRename]
  have read' := renameInto read h Δ keep
  rw [unaryRename] at read'
  have tag' := renameInto tag h Δ keep
  rw [unaryRename, numeralRename] at tag'
  have lifted := (exact_OpenRefinedAuxLeastCertificate i r (x.relabel h) (k.relabel h)
    w (y.relabel h) read' tag').1 live
  let R := refined i r
  exact edgeIntroduction ((exact_CertificateRules i (jRaw i) R (dCore i R permutation)
    false c B β Δ (x.relabel h) (y.relabel h) w).2 lifted)

#print axioms exact_OpenRefinedAuxLeastCertificate
#print axioms exact_OpenRefinedAuxLeastEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalRefinedOpenAuxFromLeastProof
