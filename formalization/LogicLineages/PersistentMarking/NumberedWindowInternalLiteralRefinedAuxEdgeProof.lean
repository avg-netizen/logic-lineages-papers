module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedAuxGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedAuxEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction actualOriginalSuccessorClosure)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalAtomicRefinement
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons z suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralRefinedAuxGuardProof (exact_OpenRefinedLiteralTagSixGuardZeros)
open NumberedWindowInternalLiteralRefinedScalarTargets (refinedLiteral)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)

open NumberedWindowComputabilityFormulaTargets (accepts)

private theorem actualAcceptsGraph {α : Type} (p : Program 3) (x w d : OTerm α) :
    accepts p x w d = programGraph p (suc z) ![x,w,d] := rfl

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem branchAST (i : Program 1) (r : Program 3) :
    refined i r =
      branch (atSource freeSource) (branch (atSource bottomSource) r (constantZero 3))
        (conjunction r (conjunction bottomTarget (atTarget i))) := by
  unfold refined
  rw [exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.2.2.2.2.1,
    exact_DispatchControlAST.1,exact_DispatchControlAST.2.2.2.2.2,
    exact_DispatchControlAST.2.2.2.2.2]

private theorem applySource (p : Program 1) (x w y : OTerm α)
    (h : Nonempty (Derivation B Γ (unary p z x))) :
    Nonempty (Derivation B Γ (programGraph (atSource p) z ![x,w,y])) := by
  unfold atSource
  apply compositionValue p (fun _ : Fin 1 => .projection (0 : Fin 3)) z ![x,w,y] ![x] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue (0 : Fin 3) ![x,w,y]

/-- On the same genuine literal tag-six auxiliary source, exactly the
unchanged old positive callback is read in the refined program. Both
directions concern actual object reports, not numerical equivalence. -/
theorem exact_OpenRefinedAuxPositive (i : Program 1) (r : Program 3)
    (ctx dom cod fn arg w dst : OTerm α) :
    let x := addressTerm ctx cod (auxiliaryTerm dom cod fn arg)
    Nonempty (Derivation B Γ (programGraph r (suc z) ![x,w,dst])) ↔
      Nonempty (Derivation B Γ (programGraph (refined i r) (suc z) ![x,w,dst])) := by
  dsimp only
  let x := addressTerm ctx cod (auxiliaryTerm dom cod fn arg)
  let xs : Fin 3 → OTerm α := ![x,w,dst]
  let q := branch (atSource bottomSource) r (constantZero 3)
  let yes := conjunction r (conjunction bottomTarget (atTarget i))
  have rejected : Nonempty (Derivation B Γ (unary freeSource z x)) ∧
      Nonempty (Derivation B Γ (unary bottomSource z x)) :=
    exact_OpenRefinedLiteralTagSixGuardZeros ctx cod
      (rawCons dom (rawCons cod (rawCons fn (rawCons arg z))))
  have hf := applySource freeSource x w dst rejected.1
  have hb := applySource bottomSource x w dst rejected.2
  rw [branchAST]
  exact ⟨fun h => zeroBranchIntro (atSource freeSource) q yes (suc z) xs hf
      (zeroBranchIntro (atSource bottomSource) r (constantZero 3) (suc z) xs hb h),
    fun h => zeroBranchElim (atSource bottomSource) r (constantZero 3) (suc z) xs hb
      (zeroBranchElim (atSource freeSource) q yes (suc z) xs hf h)⟩

abbrev lambdaAppCode (ctx dom cod rawBody arg : OTerm α) : OTerm α :=
  addressTerm ctx cod (auxiliaryTerm dom cod (lambdaTerm dom rawBody) arg)

/-- Preserve an actual supplied positive beta-instance report through
the exact installed refinement and its original coordinate wrapper.
The instance and witness are the same terms. Beta computation is not
inferred from typing or from the numeral calibration. -/
theorem exact_LiteralRefinedLambdaInstanceCertificate (i : Program 1) (r : Program 3) (c : Nat)
    (ctx dom cod rawBody arg w dst : OTerm α) :
    let x := lambdaAppCode ctx dom cod rawBody arg
    let S := refinedLiteral i r
    let Q := sourceBody S c
    Nonempty (Derivation Q Γ (programGraph r (suc z) ![x,w,dst])) ↔
      Nonempty (Derivation Q Γ (certificate S false c x dst w)) := by
  dsimp only
  let x := lambdaAppCode ctx dom cod rawBody arg
  let R := refined i r
  let Q := sourceBody (refinedLiteral i r) c
  have physical := exact_OpenRefinedAuxPositive (B := Q) (Γ := Γ) i r ctx dom cod
    (lambdaTerm dom rawBody) arg w dst
  have wrap := exact_CertificateRules i (jRaw i) R (dCore i R permutation) false c Q α Γ x dst w
  change (Nonempty (Derivation Q Γ
    (certificate (refinedLiteral i r) false c x dst w))) ↔
      Nonempty (Derivation Q Γ (accepts R x w dst)) at wrap
  rw [actualAcceptsGraph] at wrap
  exact physical.trans wrap.symm

/-- An actually held original positive beta-instance tape yields the
exact even successor at the same literal chosen body and context. -/
theorem exact_LiteralRefinedLambdaInstanceEdge (i : Program 1) (r : Program 3) (c : Nat)
    (ctx dom cod rawBody arg w dst : OTerm α)
    (real : Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ
      (programGraph r (suc z) ![lambdaAppCode ctx dom cod rawBody arg,w,dst]))) :
    Nonempty (Derivation (sourceBody (refinedLiteral i r) c) Γ
      (edge (refinedLiteral i r) false c (lambdaAppCode ctx dom cod rawBody arg) dst)) :=
  edgeIntroduction ((exact_LiteralRefinedLambdaInstanceCertificate (Γ := Γ) i r c
    ctx dom cod rawBody arg w dst).1 real)

#print axioms exact_OpenRefinedAuxPositive
#print axioms exact_LiteralRefinedLambdaInstanceCertificate
#print axioms exact_LiteralRefinedLambdaInstanceEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedAuxEdgeProof
