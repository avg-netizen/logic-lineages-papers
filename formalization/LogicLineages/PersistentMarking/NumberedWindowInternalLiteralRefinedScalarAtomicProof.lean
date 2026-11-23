module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarAtomicProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicMembershipChecks (exact_RefinedAtomicMembership)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralRefinedScalarTargets

theorem exact_TypedRefinedLiteralAtomicI : ExactTypedRefinedLiteralAtomicI := by
  constructor
  · intro i r c α Γ q ctx ty
    dsimp only
    intro typed shape
    let R := refined i r
    let D := dCore i R permutation
    let S := refinedLiteral i r
    let B := sourceBody S c
    have carries : Nonempty (Derivation B Γ (carrier S false c q)) :=
      (exact_DomainRules i (jRaw i) R D false c B α Γ q).2 typed
    exact (exact_RefinedAtomicMembership.1 i (jRaw i) r D c α Γ q ctx ty shape).1 carries
  · intro i r c α Γ q ctx ty name
    dsimp only
    intro typed shape
    let R := refined i r
    let D := dCore i R permutation
    let S := refinedLiteral i r
    let B := sourceBody S c
    have carries : Nonempty (Derivation B Γ (carrier S false c q)) :=
      (exact_DomainRules i (jRaw i) R D false c B α Γ q).2 typed
    exact (exact_RefinedAtomicMembership.2 i (jRaw i) r D c α Γ q ctx ty name shape).1 carries

#print axioms exact_TypedRefinedLiteralAtomicI
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarAtomicProof
