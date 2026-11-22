module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopLocalProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftInputs)
open NumberedWindowInternalSparseTypedRawLiftGraphProof (wrap)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof (exact_OpenCoverThinMatchingWindowInputs)
open NumberedWindowInternalCoverCombinedRestrictedRawHopTargets (thinRawAt)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem typedRawChildWindows (root other W : Program 3) (V : Program 1) (ctx ty fn child next : OTerm α)
    (raw : Nonempty (Derivation body Γ (thinRawAt (typedRaw5 root other W V) ctx ty fn child next))) :
    Nonempty (Derivation body Γ (windowAt W ctx ty fn)) ∧
    Nonempty (Derivation body Γ (windowAt W ctx ty next)) := by
  obtain ⟨exactCalls⟩ := exact_OpenTypedRaw5 body root other W V α Γ ctx ty fn child next
  obtain ⟨found⟩ := raw
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft exactCalls) found
  have ends := Derivation.conjunctionRight calls
  exact ⟨⟨Derivation.conjunctionLeft ends⟩,⟨Derivation.conjunctionRight ends⟩⟩

theorem actualWrappedRawLift (C baseW root other : Program 3) (V : Program 1) (s : Settings)
    (ctx dom cod fn child next arg : OTerm α)
    (substep : Nonempty (Derivation body Γ (thinRawAt
      (typedRaw5 root other (thinMatchingWindow C s baseW V) V) ctx (rawCons dom cod) fn child next)))
    (leftParent : Nonempty (Derivation body Γ
      (windowAt (thinMatchingWindow C s baseW V) ctx cod (auxiliaryTerm dom cod fn arg))))
    (rightParent : Nonempty (Derivation body Γ
      (windowAt (thinMatchingWindow C s baseW V) ctx cod (auxiliaryTerm dom cod next arg)))) :
    Nonempty (Derivation body Γ (thinRawAt (typedRaw5 root other (thinMatchingWindow C s baseW V) V)
      ctx cod (auxiliaryTerm dom cod fn arg) (functionWitnessTerm child) (auxiliaryTerm dom cod next arg))) := by
  let W := thinMatchingWindow C s baseW V
  let src := auxiliaryTerm dom cod fn arg
  let dst := auxiliaryTerm dom cod next arg
  have left := exact_OpenCoverThinMatchingWindowInputs C baseW V s body α Γ ctx cod src leftParent
  have right := exact_OpenCoverThinMatchingWindowInputs C baseW V s body α Γ ctx cod dst rightParent
  obtain ⟨vSrc⟩ := left.valid
  obtain ⟨vDst⟩ := right.valid
  obtain ⟨wSrc⟩ := leftParent
  obtain ⟨wDst⟩ := rightParent
  obtain ⟨raw⟩ := substep
  have actual : Nonempty (Derivation body Γ (liftInputs root other W V ctx dom cod arg fn child next)) :=
    ⟨Derivation.conjunctionIntroduction raw (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction vSrc vDst) (Derivation.conjunctionIntroduction wSrc wDst))⟩
  exact wrap root other W V ctx dom cod arg fn child next actual

#print axioms typedRawChildWindows
#print axioms actualWrappedRawLift

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRawHopLocalProof
