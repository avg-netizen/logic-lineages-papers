module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstalledCarrierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsUnionReportThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseCarrierProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalCarrierExtraction)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListInstalledCarrierProof (exact_IntroInstalledTypedCarrier)
open NumberedWindowInternalDirectTypedScratchIntroProof (exact_TypedScratchNil exact_IntroTypedScratchCons)
open NumberedWindowInternalOriginalRawConsUnionReportThinProof (actualRawConsParser)
open NumberedWindowInternalSparseFieldParserThinOpenConsProof (exact_OriginalSparseParserNil)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (oddCarrierRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)
open NumberedWindowInternalLiteralJBaseTargets

theorem exact_LiteralEmptyCarrier (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) :
    let S := literalData i r
    let B := sourceBody S c
    Nonempty (Derivation B Γ (carrier S true c (z : OTerm α))) := by
  dsimp only
  exact exact_IntroInstalledTypedCarrier i r permutation c α Γ z z
    ⟨exact_OriginalSparseParserNil,exact_TypedScratchNil i (sourceBody (literalData i r) c) α Γ⟩

theorem exact_LiteralScalarSingletonCarrier : ExactLiteralScalarSingletonCarrier := by
  intro i r c α Γ q
  dsimp only
  intro iq
  let S := literalData i r
  let B := sourceBody S c
  have even := actualOriginalCarrierExtraction S false c α Γ q iq
  have raw : Nonempty (Derivation B Γ (unary i (suc z) q)) :=
    (exact_DomainRules i (jRaw i) r (dCore i r permutation) false c B α Γ q).1 even
  apply programCases consCode ![q,z] (carrier S true c (singletonCode q))
  intro β ρ Δ out keep built
  rw [oddCarrierRename]
  simp only [singletonCode,rawConsRename,zRelabel]
  have physical : Nonempty (Derivation B Δ (programGraph consCode out ![q.relabel ρ,z])) := by
    simpa only [binaryInputsRename,zRelabel] using built
  have qc : Nonempty (Derivation B Δ (unary i (suc z) (q.relabel ρ))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto raw ρ Δ keep
  have parsed := actualRawConsParser (q.relabel ρ) z z out exact_OriginalSparseParserNil physical
  have typed := exact_IntroTypedScratchCons i B β Δ out (q.relabel ρ) z physical qc
    (exact_TypedScratchNil i B β Δ)
  exact exact_IntroInstalledTypedCarrier i r permutation c β Δ (rawCons (q.relabel ρ) z) out ⟨parsed,typed⟩

#print axioms exact_LiteralEmptyCarrier
#print axioms exact_LiteralScalarSingletonCarrier
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseCarrierProof
