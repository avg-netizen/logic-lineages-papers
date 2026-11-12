module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedArgumentObservations
open OriginalTypedArgumentObservationSwapDefinitions OriginalTypedArgumentObservationSwapSyntaxProof
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atValues (R : Program 2) (sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate observedY observedX : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (Geometry sigma tau q r rawTail rawY rawX sourceRaw targetRaw)))
 (hc : Nonempty (Derivation body Delta (Children R sigma tau q r packedQ packedR valueQ valueR typedQ typedR parameter)))
 (ho : Nonempty (Derivation body Delta (Outputs R rawTail sourceRaw targetRaw observedTail source target parameter)))
 (hk : Nonempty (Derivation body Delta (Certificate typedQ typedR observedTail rest payload certificate)))
 (hy : Nonempty (Derivation body Delta (graph2 (argumentObservations R) observedY rawY parameter)))
 (hx : Nonempty (Derivation body Delta (graph2 (argumentObservations R) observedX rawX parameter))) :
 Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) source target certificate)) := by
 have hq := andLeft hc
 have hr := andLeft (andRight hc)
 have hvq := andLeft (andRight (andRight hc))
 have hvr := andLeft (andRight (andRight (andRight hc)))
 have htq := andLeft (andRight (andRight (andRight (andRight hc))))
 have htr := andRight (andRight (andRight (andRight (andRight hc))))
 have cy := OriginalTypedArgumentObservationsInternalConsProof.forward R rawY tau r rawTail
   packedR valueR typedR observedTail parameter observedY (andLeft hg) hr hvr htr (andLeft ho) hy
 have cx := OriginalTypedArgumentObservationsInternalConsProof.forward R rawX sigma q rawTail
   packedQ valueQ typedQ observedTail parameter observedX (andLeft (andRight (andRight hg))) hq hvq htq (andLeft ho) hx
 have cxy := OriginalTypedArgumentObservationsInternalConsProof.forward R sourceRaw sigma q rawY
   packedQ valueQ typedQ observedY parameter source (andLeft (andRight hg)) hq hvq htq hy (andLeft (andRight ho))
 have cyx := OriginalTypedArgumentObservationsInternalConsProof.forward R targetRaw tau r rawX
   packedR valueR typedR observedX parameter target (andRight (andRight (andRight hg))) hr hvr htr hx (andRight (andRight ho))
 exact OriginalNumericListSortExchangeIntroductionProof.zeroPrefix
   typedQ typedR observedTail observedY observedX source target rest payload certificate
   (andLeft hk) (andLeft (andRight hk)) (andRight (andRight hk)) cy cx cxy cyx

theorem atFirst (R : Program 2) (sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate observedY : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (Geometry sigma tau q r rawTail rawY rawX sourceRaw targetRaw)))
 (hc : Nonempty (Derivation body Delta (Children R sigma tau q r packedQ packedR valueQ valueR typedQ typedR parameter)))
 (ho : Nonempty (Derivation body Delta (Outputs R rawTail sourceRaw targetRaw observedTail source target parameter)))
 (hk : Nonempty (Derivation body Delta (Certificate typedQ typedR observedTail rest payload certificate)))
 (hy : Nonempty (Derivation body Delta (graph2 (argumentObservations R) observedY rawY parameter))) :
 Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) source target certificate)) := by
 apply programCases (argumentObservations R) ![rawX,parameter] _
 intro beta rho Theta observedX hrho hx
 rw [binaryVectorRename] at hx
 simp only [graph3Rename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
 have hg' := renameInto hg rho Theta hrho
 rw [geometryRename] at hg'
 have hc' := renameInto hc rho Theta hrho
 rw [childrenRename] at hc'
 have ho' := renameInto ho rho Theta hrho
 rw [outputsRename] at ho'
 have hk' := renameInto hk rho Theta hrho
 rw [certificateRename] at hk'
 have hy' := renameInto hy rho Theta hrho
 rw [graph2Rename] at hy'
 exact atValues R (sigma.relabel rho) (tau.relabel rho) (q.relabel rho) (r.relabel rho) (rawTail.relabel rho) (rawY.relabel rho) (rawX.relabel rho) (sourceRaw.relabel rho) (targetRaw.relabel rho) (packedQ.relabel rho) (packedR.relabel rho) (valueQ.relabel rho) (valueR.relabel rho) (typedQ.relabel rho) (typedR.relabel rho) (parameter.relabel rho) (observedTail.relabel rho) (source.relabel rho) (target.relabel rho) (rest.relabel rho) (payload.relabel rho) (certificate.relabel rho) (observedY.relabel rho) observedX hg' hc' ho' hk' hy' hx

theorem actualAt (R : Program 2) (sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (Geometry sigma tau q r rawTail rawY rawX sourceRaw targetRaw)))
 (hc : Nonempty (Derivation body Delta (Children R sigma tau q r packedQ packedR valueQ valueR typedQ typedR parameter)))
 (ho : Nonempty (Derivation body Delta (Outputs R rawTail sourceRaw targetRaw observedTail source target parameter)))
 (hk : Nonempty (Derivation body Delta (Certificate typedQ typedR observedTail rest payload certificate)))
 : Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) source target certificate)) := by
 apply programCases (argumentObservations R) ![rawY,parameter] _
 intro beta rho Theta observedY hrho hy
 rw [binaryVectorRename] at hy
 simp only [graph3Rename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
 have hg' := renameInto hg rho Theta hrho
 rw [geometryRename] at hg'
 have hc' := renameInto hc rho Theta hrho
 rw [childrenRename] at hc'
 have ho' := renameInto ho rho Theta hrho
 rw [outputsRename] at ho'
 have hk' := renameInto hk rho Theta hrho
 rw [certificateRename] at hk'
 exact atFirst R (sigma.relabel rho) (tau.relabel rho) (q.relabel rho) (r.relabel rho) (rawTail.relabel rho) (rawY.relabel rho) (rawX.relabel rho) (sourceRaw.relabel rho) (targetRaw.relabel rho) (packedQ.relabel rho) (packedR.relabel rho) (valueQ.relabel rho) (valueR.relabel rho) (typedQ.relabel rho) (typedR.relabel rho) (parameter.relabel rho) (observedTail.relabel rho) (source.relabel rho) (target.relabel rho) (rest.relabel rho) (payload.relabel rho) (certificate.relabel rho) observedY hg' hc' ho' hk' hy

theorem actualSwap : OriginalTypedArgumentObservationSwapTargets.ActualSwap := by
 intro R body alpha sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate
 let H := Geometry sigma tau q r rawTail rawY rawX sourceRaw targetRaw ⊓
  (Children R sigma tau q r packedQ packedR valueQ valueR typedQ typedR parameter ⊓
  (Outputs R rawTail sourceRaw targetRaw observedTail source target parameter ⊓
   Certificate typedQ typedR observedTail rest payload certificate))
 have h : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hh⟩ := actualAt R sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate (andLeft h) (andLeft (andRight h))
   (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
 exact ⟨Derivation.implicationIntroduction hh⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapProof
