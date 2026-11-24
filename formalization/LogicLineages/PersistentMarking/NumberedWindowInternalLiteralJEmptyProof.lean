module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseCarrierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptyCertificateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (certificate edge membership)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralJBaseCarrierProof (exact_LiteralEmptyCarrier)
open NumberedWindowInternalLiteralJEmptyCertificateProof (exact_LiteralEmptyCertificateImpossible)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (oddIntroduction oddCertificateCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalLiteralJBaseTargets

theorem exact_LiteralEmptyJ : ExactLiteralEmptyJ := by
  intro i r c α Γ
  dsimp only
  intro reverse
  let S := literalData i r
  let B := sourceBody S c
  apply oddIntroduction S c Γ z (exact_LiteralEmptyCarrier i r c α Γ)
  intro β ρ Δ dst _ strict
  have edge0 : Nonempty (Derivation B Δ (edge S true c z dst)) := by
    simpa only [zRelabel] using strict
  apply oddCertificateCases S c Δ z dst (membership true dst) edge0
  intro γ τ Ω w _ cert
  have cert0 : Nonempty (Derivation B Ω (certificate S true c z (dst.relabel τ) w)) := by
    simpa only [zRelabel] using cert
  obtain ⟨bad⟩ := exact_LiteralEmptyCertificateImpossible i r c γ Ω (dst.relabel τ) w reverse cert0
  rw [membershipRename]
  exact ⟨Derivation.explosion bad⟩

#print axioms exact_LiteralEmptyJ
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptyProof
