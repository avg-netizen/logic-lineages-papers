module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJBaseTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptyCertificateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport outputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (refl cancelSuc sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalQuotientComparisonProof (orRight)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserThinOpenConsProof (exact_OriginalSparseParserNil)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalScratchAppendOpenSyntaxProof (appendRename)
open NumberedWindowInternalScratchAppendOpenChecks (exact_OpenScratchAppendMembership)
open NumberedWindowInternalDirectCoreInstalledCertificateProof (exact_InstalledCertificateSharedTape)
open NumberedWindowInternalDirectBoundaryOpenProof (exact_OpenRawGuards)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralJBaseTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem noSourceMember (s key : OTerm α)
    (ps : Nonempty (Derivation B Γ (unary parser (suc s) z)))
    (mem : Nonempty (Derivation B Γ (memberGraph s key))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  obtain ⟨same⟩ := valueUnique parser (suc s) (suc z) ![z] ps exact_OriginalSparseParserNil
  have impossible : Nonempty (Derivation B Γ (memberGraph z key)) :=
    headTransport scratchMember (suc z) s z ![key] ⟨cancelSuc same⟩ mem
  have positive := nilRecover memberBase memberStep (suc z) ![key] impossible
  obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![key] positive (constantZeroValue ![key])
  exact ⟨sucNeZeroApply bad⟩

private theorem fromRemovedCons (reverse : LiteralReverseMembership B)
    (removed s k d sk seen head tail : OTerm α)
    (ps : Nonempty (Derivation B Γ (unary parser (suc s) z)))
    (pd : Nonempty (Derivation B Γ (unary parser (suc d) removed)))
    (pr : Nonempty (Derivation B Γ (unary parser (suc seen) removed)))
    (cell : Nonempty (Derivation B Γ (consGraph seen head tail)))
    (appended : Nonempty (Derivation B Γ (appendGraph sk k d)))
    (observed : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![s,sk]))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  obtain ⟨same⟩ := valueUnique parser (suc seen) (suc d) ![removed] pr pd
  have actual : Nonempty (Derivation B Γ (consGraph d head tail)) :=
    outputTransport consCode seen d (Fin.cons head (Fin.cons tail Fin.elim0)) ⟨cancelSuc same⟩ cell
  obtain ⟨member⟩ := headMember d head tail head actual ⟨refl head⟩
  have joined := exact_OpenScratchAppendMembership B α Γ k d sk head appended ⟨orRight member⟩
  exact noSourceMember s head ps (reverse α Γ s sk head observed joined)

theorem exact_LiteralEmptyCertificateImpossible : ExactLiteralEmptyCertificateImpossible := by
  intro i r c α Γ dst w
  dsimp only
  intro reverse cert
  let S := literalData i r
  let B := sourceBody S c
  apply exact_InstalledCertificateSharedTape i (jRaw i) r permutation c α Γ z w dst (⊥ : Formula α) cert
  intro β ρ Δ kept removed inserted s t k d a p sk tp _ _ _ boundary reports
  change Nonempty (Derivation B Δ (⊥ : Formula β))
  have source : Nonempty (Derivation B Δ (unary parser (suc s) z)) := by
    simpa only [zRelabel] using reports.sourceParsed
  rw [zRelabel] at boundary
  apply exact_OpenRawGuards i B β Δ z (dst.relabel ρ) removed (⊥ : Formula β) boundary
  intro γ τ Ω ds dt seen hd tl keep found
  have ps : Nonempty (Derivation B Ω (unary parser (suc (s.relabel τ)) z)) := by
    simpa only [zRelabel] using renameParser (z : OTerm β) s source τ Ω keep
  have pd := renameParser removed d reports.removedParsed τ Ω keep
  have ap : Nonempty (Derivation B Ω (appendGraph (sk.relabel τ) (k.relabel τ) (d.relabel τ))) := by
    simpa only [appendRename] using renameInto reports.sourceAppend τ Ω keep
  have measured : Nonempty (Derivation B Ω
    (programGraph permutation (suc z) ![s.relabel τ,sk.relabel τ])) := by
    simpa only [sucRelabel,zRelabel] using
      renamePair permutation (suc z) s sk reports.sourceObserved τ keep
  change Nonempty (Derivation B Ω (⊥ : Formula γ))
  exact fromRemovedCons reverse (removed.relabel τ) (s.relabel τ) (k.relabel τ)
    (d.relabel τ) (sk.relabel τ) seen hd tl ps pd found.parsed.removed found.removedCons ap measured

#print axioms exact_LiteralEmptyCertificateImpossible
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptyCertificateProof
