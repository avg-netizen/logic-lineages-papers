module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaOwnRunCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedRawFunctionLiftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDualTypedRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaTypedRawCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawTick (rootCall rootTest)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (exact_OpenLiteralAtomicRawUnderlying)
open NumberedWindowInternalLiteralDualTypedRawProof (dualTypedRaw exact_OpenDualTypedRawEndpoints)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
  (joinedAuxiliaryWindow selectedBiAuxCoveredWindow exact_OpenJoinedAuxiliaryWindow)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (selectedBiAuxWindow)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFallback)
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof (LambdaParts)
open NumberedWindowInternalLiteralLambdaContextOwnRunProof (fullLambdaFallback)
open NumberedWindowInternalLiteralLambdaOwnRunCasesProof (exact_OpenLambdaOwnRunCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- General raw lambda-step inversion on the actual dual typed checker.
The original lexical windows stay at the actual parent endpoints.
The contextual alternative has the exact body run below the binder;
typing and selecting the body in its extended context are separate. -/
theorem exact_OpenLambdaTypedRawCases (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (ctx ty q w r : OTerm α) (goal : Formula α) :
    let raw := selectedJoinedRaw s base T V TV baseM leaf (lambdaFallback other)
    let P := atomicRoot (root (leafAtAuxiliary leaf))
    let Q := joinedAuxiliaryWindow s base T V TV baseM
    D B Γ (unary cellHead (numeral 2) q) →
    D B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r]) →
    (D B Γ (windowAt Q ctx ty q) → D B Γ (windowAt Q ctx ty r) →
      (∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        D B Δ (bit rootTest ![q.relabel j,w.relabel j,r.relabel j]) →
        D B Δ (bit (rootCall P) ![q.relabel j,w.relabel j,r.relabel j]) → D B Δ (goal.relabel j))) →
    (D B Γ (windowAt Q ctx ty q) → D B Γ (windowAt Q ctx ty r) →
      (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d a inner e b : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        LambdaParts B Δ (q.relabel j) (w.relabel j) (r.relabel j) d a inner e b →
        D B Δ (bit (ownRun P (fullLambdaFallback other)) ![a,inner,b]) → D B Δ (goal.relabel j))) →
    D B Γ goal := by
  intro raw P Q header steps rootCase contextCase
  let A := selectedBiAuxCoveredWindow s base T V TV baseM
  let Z := selectedBiAuxWindow s base T V TV baseM
  let Va := unitAuxSyntax V TV
  let P₀ := root (leafAtAuxiliary leaf)
  let F := fallback (lambdaFallback other)
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  have old := exact_OpenLiteralAtomicRawUnderlying (dualTypedRaw P₀ F A Z Va) xs steps
  obtain ⟨outer⟩ := exact_OpenDualTypedRawEndpoints P₀ F A Z Va ctx ty q w r old
  obtain ⟨codec⟩ := exact_OpenTypedRaw5 B P (fullLambdaFallback other) A Va α Γ ctx ty q w r
  have fields := Derivation.implicationElimination (Derivation.conjunctionLeft codec) (Derivation.conjunctionLeft outer)
  let strict := Derivation.conjunctionRight outer
  let window := Derivation.conjunctionRight fields
  have a := (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty q).mpr
    ⟨⟨Derivation.conjunctionLeft strict⟩,⟨Derivation.conjunctionLeft window⟩⟩
  have b := (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty r).mpr
    ⟨⟨Derivation.conjunctionRight strict⟩,⟨Derivation.conjunctionRight window⟩⟩
  exact exact_OpenLambdaOwnRunCases P other q w r goal header
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft fields)⟩
    (rootCase a b) (contextCase a b)

#print axioms exact_OpenLambdaTypedRawCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaTypedRawCasesProof
