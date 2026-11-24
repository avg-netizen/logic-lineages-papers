module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressCarrierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchParserProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCarrierReflectionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.SourcePresentation (sourceBody)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedListOpenProof (exact_OpenJRaw)
open NumberedWindowInternalDirectTypedScratchMemberProof (exact_TypedScratchMember)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)
open NumberedWindowInternalLiteralSingletonStepProof (singletonCodeRename)
open NumberedWindowInternalLiteralSingletonScratchParserProof (exact_ParsedSingletonScratch)
open NumberedWindowInternalLiteralSingletonProgressCarrierProof (exact_LiteralSingletonCarrierFromScalar)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

/-- Literal singleton carrier and its scalar carrier are equivalent on
their actual code at arbitrary open terms in this same body. -/
theorem exact_LiteralSingletonCarrierReflection (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (q : OTerm α) :
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (carrier S true c (singletonCode q)) ↔ D B Γ (carrier S false c q) := by
  dsimp only
  refine ⟨?_,exact_LiteralSingletonCarrierFromScalar i r c α Γ q⟩
  intro odd
  let S := literalData i r
  let B := sourceBody S c
  have parsed := (exact_DomainRules i (jRaw i) r (dCore i r permutation) true c B α Γ
    (singletonCode q)).1 odd
  apply exact_OpenJRaw i B α Γ (singletonCode q) (carrier S false c q) parsed
  intro β j Δ code _ reports
  rw [carrierRename]
  have literal := reports.parsed
  rw [singletonCodeRename] at literal
  have cell := exact_ParsedSingletonScratch B β Δ (q.relabel j) code literal
  obtain ⟨inside⟩ := headMember code (q.relabel j) z (q.relabel j) cell ⟨refl _⟩
  obtain ⟨rule⟩ := exact_TypedScratchMember i B β Δ code (q.relabel j)
  obtain ⟨typed⟩ := reports.typed
  exact (exact_DomainRules i (jRaw i) r (dCore i r permutation) false c B β Δ (q.relabel j)).2
    ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction typed inside)⟩

#print axioms exact_LiteralSingletonCarrierReflection
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCarrierReflectionProof
