module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginSharedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchParserProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginInstalledProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectCoreInstalledCertificateProof (exact_InstalledCertificateSharedTape)
open NumberedWindowInternalDirectBoundaryOpenProof (exact_OpenRawGuards)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectProjectedCertSyntaxProof (renameShared)
open NumberedWindowInternalDirectInstalledOriginSyntaxProof (targetMember)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)
open NumberedWindowInternalLiteralSingletonScratchParserProof (exact_ParsedSingletonScratch)
open NumberedWindowInternalLiteralSingletonOriginSharedProof (exact_LiteralSingletonMemberEdgeFromShared)
open NumberedWindowInternalLiteralSingletonOriginTargets

theorem exact_InstalledLiteralSingletonMemberEdge : ExactInstalledLiteralSingletonMemberEdge := by
  intro i r c α Γ head dst w decoded key
  dsimp only
  intro cert parsed member
  let S := literalData i r
  let B := sourceBody S c
  apply exact_InstalledCertificateSharedTape i (jRaw i) r permutation c α Γ
    (singletonCode head) w dst (edge S false c head key) cert
  intro β ρ Δ kept removed inserted s t k d a p sk tp keep _ _ boundary reports
  rw [edgeRename]
  let G := edge S false c (head.relabel ρ) (key.relabel ρ)
  let raw := (singletonCode head).relabel ρ
  let targetRaw := dst.relabel ρ
  let needle := key.relabel ρ
  have known := renameParser dst decoded parsed ρ Δ keep
  have held := renameInto member ρ Δ keep
  rw [graphRename] at held
  have atTarget := targetMember targetRaw (decoded.relabel ρ) t needle known reports.targetParsed held
  apply exact_OpenRawGuards i B β Δ raw targetRaw removed G boundary
  intro γ τ Ω _ _ d' h tail retain guarded
  change Nonempty (Derivation B Ω ((edge S false c (head.relabel ρ) (key.relabel ρ)).relabel τ))
  rw [edgeRename]
  have shared := renameShared permutation permutation r raw targetRaw kept removed inserted
    s t k d a p sk tp reports τ retain
  have observed := renameParser removed d reports.removedParsed τ Ω retain
  obtain ⟨same⟩ := valueUnique parser (suc d') (suc (d.relabel τ)) ![removed.relabel τ]
    guarded.parsed.removed observed
  have genuine : Nonempty (Derivation B Ω (consGraph (d.relabel τ) h tail)) :=
    outputTransport consCode d' (d.relabel τ) (Fin.cons h (Fin.cons tail Fin.elim0))
      ⟨cancelSuc same⟩ guarded.removedCons
  have removing := headMember (d.relabel τ) h tail h genuine ⟨refl h⟩
  have idSrc : Nonempty (Derivation B Ω (unary parser (suc (s.relabel τ))
      (singletonCode ((head.relabel ρ).relabel τ)))) := by
    simpa only [raw,singletonCode,rawConsRename,zRelabel] using shared.sourceParsed
  have con := exact_ParsedSingletonScratch B γ Ω ((head.relabel ρ).relabel τ) (s.relabel τ) idSrc
  have hit : Nonempty (Derivation B Ω (memberGraph (t.relabel τ) (needle.relabel τ))) := by
    simpa only [graphRename] using renameInto atTarget τ Ω retain
  exact exact_LiteralSingletonMemberEdgeFromShared i r c γ Ω
    (raw.relabel τ) (targetRaw.relabel τ) (kept.relabel τ) (removed.relabel τ) (inserted.relabel τ)
    (s.relabel τ) (t.relabel τ) (k.relabel τ) (d.relabel τ)
    (a.relabel τ) (p.relabel τ) (sk.relabel τ) (tp.relabel τ)
    ((head.relabel ρ).relabel τ) h (needle.relabel τ) shared con removing hit

#print axioms exact_InstalledLiteralSingletonMemberEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginInstalledProof
