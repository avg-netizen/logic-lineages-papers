module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoGuardedChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (admitted)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (unaryValue)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoveredWindowTargets (contextPresent ownSeed)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalAuxExchangeMemoGuardedChecks (exact_OpenGuardedAuxMemoLift)
open NumberedWindowInternalSparseCoveredInstallationChecks (exact_CoveredEdgeValues)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalSparseStructuralApplicationTargets

attribute [local irreducible] programGraph

theorem exact_SyntaxWindowCalibration : ExactSyntaxWindowCalibration := by
  intro s baseW V original valid ctx ty seed
  rw [syntaxWindow,actualConjunctionEvaluation,original]
  cases h : packedWindow s ctx ty seed with
  | false => rfl
  | true =>
    have syntaxTrue : (syntaxBits seed).1 = true := by
      cases u : unpack ctx with
      | none => simp [packedWindow,u] at h
      | some xs =>
        have ok : admitted s xs ty seed = true := by simpa [packedWindow,u] using h
        exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).2).1
    rw [unaryValue]
    change (if 1 = 1 ∧ evaluate V (seed ::ᵥ nil) = 1 then 1 else 0) = _
    exact if_pos ⟨rfl,(valid seed).trans (by rw [syntaxTrue]; rfl)⟩

theorem exact_WindowSyntaxReport : ExactWindowSyntaxReport := by
  intro C s baseW V body α Γ ctx ty seed
  let xs := ![ctx,ty,seed]
  let W := window C s baseW V
  let A := windowAt W ctx ty seed
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨outer⟩ := conjunctionRecover (syntaxWindow baseW V) (conjunction contextPresent (ownSeed C s)) xs ⟨h⟩
  obtain ⟨inner⟩ := conjunctionRecover baseW (.composition V (fun _ : Fin 1 => .projection 2)) xs ⟨Derivation.conjunctionLeft outer⟩
  obtain ⟨result⟩ := compositionRecover V (fun _ : Fin 1 => .projection 2) (suc z) xs ![seed]
    ⟨Derivation.conjunctionRight inner⟩ (by
      intro n
      obtain rfl := Fin.eq_zero n
      exact projectionValue 2 xs)
  exact ⟨Derivation.implicationIntroduction result⟩

theorem exact_StructuralFunctionEdge : ExactStructuralFunctionEdge := by
  intro C s base baseW V body α Γ ctx dom cod f g arg left right value a b E source
  let W := window C s baseW V
  let X := exchange C s base V
  let Δ := source :: Γ
  have h : Derivation body Δ source := Derivation.hypothesis List.mem_cons_self
  obtain ⟨child⟩ := exact_OpenPackedScalarEdge X W body α Δ ctx (rawCons dom cod) f g
  have x := Derivation.conjunctionLeft (Derivation.implicationElimination (Derivation.conjunctionLeft child) (Derivation.conjunctionLeft h))
  have reports := Derivation.conjunctionRight h
  have ws := Derivation.conjunctionLeft reports
  obtain ⟨leftSyntax⟩ := exact_WindowSyntaxReport C s baseW V body α Δ ctx cod a
  obtain ⟨rightSyntax⟩ := exact_WindowSyntaxReport C s baseW V body α Δ ctx cod b
  have ls := Derivation.implicationElimination leftSyntax (Derivation.conjunctionLeft ws)
  have rs := Derivation.implicationElimination rightSyntax (Derivation.conjunctionRight ws)
  obtain ⟨lifted⟩ := exact_OpenGuardedAuxMemoLift C s base V body α Δ dom cod f g arg left right
  have exchanged := Derivation.implicationElimination lifted (Derivation.conjunctionIntroduction x
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction ls rs) (Derivation.conjunctionRight reports)))
  obtain ⟨parent⟩ := exact_OpenPackedScalarEdge X W body α Δ ctx cod a b
  have edge := Derivation.implicationElimination (Derivation.conjunctionRight parent)
    (Derivation.conjunctionIntroduction exchanged ws)
  obtain ⟨law⟩ := exact_CoveredEdgeValues C s (selected (step base V)) (syntaxWindow baseW V) body α Δ ctx cod a b value
  have transfer := Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.implicationElimination law edge))
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction edge transfer)⟩

#print axioms exact_SyntaxWindowCalibration
#print axioms exact_WindowSyntaxReport
#print axioms exact_StructuralFunctionEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationChecks
