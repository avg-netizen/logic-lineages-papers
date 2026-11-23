module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (membership)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreReinstallTargets (Reinstalled)
open NumberedWindowInternalDirectCoreNumericTargets (PositiveFit)
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)

abbrev refinedLiteral (i : Program 1) (r : Program 3) : Data := literalData i (refined i r)

/-- The fresh chosen even refinement and chosen odd programs are present
together in the same original numeric interpretation; no old proofs moved. -/
def ExactReinstallLiteralRefinedScalar : Prop :=
  ∀ (xs : Entries) (s : Settings) (i : Program 1) (r : Program 3),
    ScalarFit i (checks xs s).scalar → PositiveFit r (checks xs s).positive →
    Reinstalled xs s i (jRaw i) (refined i r) permutation

/-- Actual symbolic atomic I for this exact new body, given the actual
scalar typed bit and an exact original packed shape. -/
def ExactTypedRefinedLiteralAtomicI : Prop :=
  (∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α)) (q ctx ty : OTerm α),
    let S := refinedLiteral i r
    let B := sourceBody S c
    Nonempty (Derivation B Γ (unary i (suc z) q)) →
    Nonempty (Derivation B Γ (equal q (packedBottomTerm ctx ty))) →
    Nonempty (Derivation B Γ (membership false q))) ∧
  (∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α)) (q ctx ty name : OTerm α),
    let S := refinedLiteral i r
    let B := sourceBody S c
    Nonempty (Derivation B Γ (unary i (suc z) q)) →
    Nonempty (Derivation B Γ (equal q (packedFreeTerm ctx ty name))) →
    Nonempty (Derivation B Γ (membership false q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
