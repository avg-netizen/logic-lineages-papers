module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaTypedLiftProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparseRawLambdaFrame (endpointTerm witnessTerm)
open NumberedWindowInternalSparseRawLambdaRun (lambdaFallback)
open NumberedWindowInternalSparseRawLambdaRunProof (exact_OpenLambdaOwnRunLift)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- On the exact same selected raw root/fallback and the same syntax and
window programs, a genuine typed body step at the literal pushed
lexical context lifts through the original lambda frame. The four new
actual parent endpoint guard reports remain explicit. -/
theorem exact_OpenTypedRaw5LambdaLift (root other W : Program 3) (syn : Program 1)
    (ctx dom result src child dst : OTerm α)
    (bodyStep : Nonempty (Derivation B Γ
      (programGraph (typedRaw5 root (lambdaFallback other) W syn) (suc z)
        ![rawCons dom ctx,result,src,child,dst])))
    (parent : Nonempty (Derivation B Γ
      (liftedEndpointGuards W syn ctx (rawCons dom result) (endpointTerm dom src) (endpointTerm dom dst)))) :
    Nonempty (Derivation B Γ
      (programGraph (typedRaw5 root (lambdaFallback other) W syn) (suc z)
        ![ctx,rawCons dom result,endpointTerm dom src,witnessTerm child,endpointTerm dom dst])) := by
  let Q := lambdaFallback other
  let lhs := endpointTerm dom src
  let rhs := endpointTerm dom dst
  let wit := witnessTerm child
  obtain ⟨d⟩ := bodyStep
  obtain ⟨guard⟩ := parent
  obtain ⟨oldCut⟩ := exact_OpenTypedRaw5 B root Q W syn α Γ (rawCons dom ctx) result src child dst
  have facts := Derivation.implicationElimination (Derivation.conjunctionLeft oldCut) d
  obtain ⟨lifted⟩ := exact_OpenLambdaOwnRunLift B root other α Γ dom src child dst z
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft facts)⟩
  obtain ⟨newCut⟩ := exact_OpenTypedRaw5 B root Q W syn α Γ ctx (rawCons dom result) lhs wit rhs
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight newCut)
    (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft guard) lifted)
      (Derivation.conjunctionRight guard))⟩

#print axioms exact_OpenTypedRaw5LambdaLift
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaTypedLiftProof
