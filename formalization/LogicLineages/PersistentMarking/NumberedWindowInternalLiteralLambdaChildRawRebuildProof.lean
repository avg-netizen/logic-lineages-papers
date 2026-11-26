module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaTypedRawCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoObservationsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedGuardReturnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDualTypedRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaChildRawRebuildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFallback)
open NumberedWindowInternalLiteralLambdaContextOwnRunProof (fullLambdaFallback)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
  (joinedAuxiliaryWindow selectedBiAuxCoveredWindow exact_OpenJoinedAuxiliaryWindow)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (selectedBiAuxWindow)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralCoveredMemoObservationsProof (exact_OpenCoveredMemoObservations)
open NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof (auxiliaryAtomicTypedRaw)
open NumberedWindowInternalLiteralDualTypedRawProof (dualTypedRaw exact_OpenDualTypedRawAtoms)
open NumberedWindowInternalLiteralAtomicTypedGuardReturnProof (exact_OpenLiteralRawGuardReturnFromAtoms)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Reassemble the original selected raw checker on the exact child
witness and both actual child windows. Syntax is recovered from the
covered memo of each child, not inferred from a numerical equivalence. -/
theorem exact_OpenRebuildLambdaChildRaw (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (ctx ty a w b : OTerm α) :
    let Q := joinedAuxiliaryWindow s base T V TV baseM
    let P := atomicRoot (root (leafAtAuxiliary leaf))
    D B Γ (windowAt Q ctx ty a) → D B Γ (windowAt Q ctx ty b) →
    D B Γ (bit (ownRun P (fullLambdaFallback other)) ![a,w,b]) →
    D B Γ (programGraph (selectedJoinedRaw s base T V TV baseM leaf (lambdaFallback other))
      (suc z) ![ctx,ty,a,w,b]) := by
  intro Q P left right own
  let C := measuredStrictCover V TV baseM
  let Va := unitAuxSyntax V TV
  let A := selectedBiAuxCoveredWindow s base T V TV baseM
  let Z := selectedBiAuxWindow s base T V TV baseM
  let P₀ := root (leafAtAuxiliary leaf)
  let F := fallback (lambdaFallback other)
  let raw := dualTypedRaw P₀ F A Z Va
  obtain ⟨lZ,lA⟩ := (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty a).mp left
  obtain ⟨rZ,rA⟩ := (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty b).mp right
  obtain ⟨sa⟩ := exact_OpenCoveredMemoObservations C s base T Va ctx ty a lA
  obtain ⟨sb⟩ := exact_OpenCoveredMemoObservations C s base T Va ctx ty b rA
  obtain ⟨o⟩ := own
  have buildChild (W : Program 3) (l : D B Γ (windowAt W ctx ty a)) (r : D B Γ (windowAt W ctx ty b)) :
      D B Γ (programGraph (auxiliaryAtomicTypedRaw P₀ F W Va) (suc z) ![ctx,ty,a,w,b]) := by
    obtain ⟨codec⟩ := exact_OpenTypedRaw5 B P (fullLambdaFallback other) W Va α Γ ctx ty a w b
    obtain ⟨x⟩ := l
    obtain ⟨y⟩ := r
    have sy := Derivation.conjunctionIntroduction (Derivation.conjunctionRight sa) (Derivation.conjunctionRight sb)
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight codec)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction sy o)
        (Derivation.conjunctionIntroduction x y))⟩
  have both : D B Γ (programGraph raw (suc z) ![ctx,ty,a,w,b]) :=
    conjunctionAccept (auxiliaryAtomicTypedRaw P₀ F A Va) (auxiliaryAtomicTypedRaw P₀ F Z Va)
      ![ctx,ty,a,w,b] (buildChild A lA rA) (buildChild Z lZ rZ)
  exact exact_OpenLiteralRawGuardReturnFromAtoms raw (exact_OpenDualTypedRawAtoms P₀ F A Z Va) ctx ty a w b both

#print axioms exact_OpenRebuildLambdaChildRaw
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaChildRawRebuildProof
