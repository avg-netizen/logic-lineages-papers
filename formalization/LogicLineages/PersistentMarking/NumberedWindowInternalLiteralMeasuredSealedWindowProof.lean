module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoverageAtTypeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMeasuredSealedWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window coveredWindow syntaxWindow)
open NumberedWindowInternalLiteralSealedWindowProof (sealedWindow exact_OpenSealedWindow)
open NumberedWindowInternalLiteralCoverageOptionProof (exact_OpenFactoredSyntaxFromCoverage)
open NumberedWindowInternalLiteralCoverageAtTypeProof (exact_OpenCoverageTypeRetape)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The strict sealed checker and the measured window built on the
very same base and same factored cover have interderivable acceptance.
The extra raw syntax report is retrieved from the actual original cover,
so the old raw inversion has no new syntax premise. -/
theorem exact_OpenFactoredSealedWindow (V M : Program 1) (G U : Program 3)
    (s : Settings) (ctx ty q : OTerm α) :
    let C := factoredCover (normalize V) M G
    D B Γ (windowAt (sealedWindow C s U) ctx ty q) ↔
      D B Γ (windowAt (window C s U (normalize V)) ctx ty q) := by
  intro C
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let Q := conjunction contextPresent (ownSeed C s)
  let Vt : Program 3 := .composition (normalize V) (fun _ : Fin 1 => .projection 2)
  constructor
  · intro held
    obtain ⟨base,cover⟩ := (exact_OpenSealedWindow C s U ctx ty q).1 held
    have raw := exact_OpenFactoredSyntaxFromCoverage V M G s ctx q cover
    have raw' : D B Γ (programGraph Vt (suc z) xs) := by
      apply compositionValue (normalize V) (fun _ : Fin 1 => .projection 2) (suc z) xs ![q] raw
      intro i
      obtain rfl := Fin.eq_zero i
      exact projectionValue 2 xs
    have checks := exact_OpenCoverageTypeRetape C s ctx z ty q cover
    exact conjunctionAccept (syntaxWindow U (normalize V)) Q xs
      (conjunctionAccept U Vt xs base raw') checks
  · intro held
    obtain ⟨both⟩ := conjunctionRecover (syntaxWindow U (normalize V)) Q xs held
    obtain ⟨bs⟩ := conjunctionRecover U Vt xs ⟨Derivation.conjunctionLeft both⟩
    have cover : D B Γ (coverageReport C s ctx q) :=
      exact_OpenCoverageTypeRetape C s ctx ty z q ⟨Derivation.conjunctionRight both⟩
    exact (exact_OpenSealedWindow C s U ctx ty q).2 ⟨Derivation.conjunctionLeft bs⟩ cover

#print axioms exact_OpenFactoredSealedWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMeasuredSealedWindowProof
