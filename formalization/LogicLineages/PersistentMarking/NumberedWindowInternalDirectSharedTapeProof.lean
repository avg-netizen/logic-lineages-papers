module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionAppendProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTape
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough renameParser renameUnit)
open NumberedWindowInternalDirectSourcePartitionRawProof (exact_OpenRawSourceDecode)
open NumberedWindowInternalDirectSourcePartitionAppendProof (exact_OpenSourcePartitionAppend)
open NumberedWindowInternalDirectTargetPartitionRawTargets (rawTargetCheck)
open NumberedWindowInternalDirectTargetPartitionRawProof (exactOpenRawTargetCheck)
open NumberedWindowInternalDirectInsertedScanTargets (scan)
open NumberedWindowInternalDirectInsertedScan (exactOpenScanParser)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalDirectSharedTapeTargets
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair commonAppend)

attribute [local irreducible] programGraph

private theorem joinAtSource (sourceObserver targetObserver : Program 2) (r : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (src dst kept removed inserted s k d sk : OTerm α) (goal : Formula α)
    (p : ParsedTriplet B Γ src kept removed s k d)
    (sa : Nonempty (Derivation B Γ (programGraph append sk ![k,d])))
    (so : Nonempty (Derivation B Γ (programGraph sourceObserver (suc z) ![s,sk])))
    (target : Nonempty (Derivation B Γ (programGraph (rawTargetCheck targetObserver)
      (suc z) (sourceTape dst kept inserted))))
    (sc : Nonempty (Derivation B Γ (programGraph (scan r) oneTerm ![inserted,removed])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (s t k d a p sk tp : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Reports sourceObserver targetObserver r B Δ (src.relabel j) (dst.relabel j) (kept.relabel j)
        (removed.relabel j) (inserted.relabel j) s t k d a p sk tp →
      Nonempty (Derivation B Δ (goal.relabel j))) : Nonempty (Derivation B Γ goal) := by
  apply exactOpenRawTargetCheck targetObserver B α Γ dst kept inserted goal target
  intro β j Δ t targetK a projected tp keep strip
  have s' := renameParser src s p.source j Δ keep
  have k' := renameParser kept k p.kept j Δ keep
  have d' := renameParser removed d p.removed j Δ keep
  have sa' := renamePair append sk k d sa j keep
  have so' : Nonempty (Derivation B Δ (programGraph sourceObserver (suc z)
      ![s.relabel j,sk.relabel j])) := by
    simpa only [sucRelabel,zRelabel] using renamePair sourceObserver (suc z) s sk so j keep
  have sc' : Nonempty (Derivation B Δ (programGraph (scan r) oneTerm
      ![inserted.relabel j,removed.relabel j])) := by
    simpa only [oneTerm,sucRelabel,zRelabel] using renamePair (scan r) oneTerm inserted removed sc j keep
  have ta := commonAppend (kept.relabel j) (k.relabel j) targetK projected tp
    k' strip.keptReport strip.appendReport
  have l := exactOpenScanParser r B β Δ (inserted.relabel j) (removed.relabel j)
    a strip.insertedReport sc'
  exact next β j Δ (s.relabel j) t (k.relabel j) (d.relabel j) a projected (sk.relabel j) tp keep
    ⟨s',strip.targetReport,k',d',strip.insertedReport,strip.rawMapReport,
      strip.scratchMapReport,sa',ta,so',strip.observerReport,l⟩

theorem exactOpenSharedTape : ExactOpenSharedTape := by
  intro sourceObserver targetObserver r B α Γ src dst kept removed inserted goal source target sc next
  apply exact_OpenRawSourceDecode (observePartition sourceObserver) B α Γ src kept removed goal source
  intro β j Δ s k d keep p core
  apply exact_OpenSourcePartitionAppend sourceObserver s k d (goal.relabel j) core
  intro γ l Ω sk retain sa so
  let ρ := l ∘ j
  have keepρ := keepThrough j l keep retain
  have shared : ParsedTriplet B Ω (src.relabel ρ) (kept.relabel ρ) (removed.relabel ρ)
      (s.relabel l) (k.relabel l) (d.relabel l) := by
    have pS := renameParser (src.relabel j) s p.source l Ω retain
    have pK := renameParser (kept.relabel j) k p.kept l Ω retain
    have pD := renameParser (removed.relabel j) d p.removed l Ω retain
    exact ⟨by simpa only [ρ,Term.relabel_relabel] using pS,
      by simpa only [ρ,Term.relabel_relabel] using pK,
      by simpa only [ρ,Term.relabel_relabel] using pD⟩
  have target' := renameUnit (rawTargetCheck targetObserver) dst kept inserted target ρ Ω keepρ
  have sc' : Nonempty (Derivation B Ω (programGraph (scan r) oneTerm
      ![inserted.relabel ρ,removed.relabel ρ])) := by
    simpa only [oneTerm,sucRelabel,zRelabel] using
      renamePair (scan r) oneTerm inserted removed sc ρ keepρ
  rw [formulaRelabelComposition]
  apply joinAtSource sourceObserver targetObserver r B γ Ω (src.relabel ρ) (dst.relabel ρ)
    (kept.relabel ρ) (removed.relabel ρ) (inserted.relabel ρ) (s.relabel l) (k.relabel l)
    (d.relabel l) sk (goal.relabel ρ) shared sa so target' sc'
  intro δ m Ξ S T K D A P SK TP preserve report
  rw [formulaRelabelComposition]
  apply next δ (m ∘ ρ) Ξ S T K D A P SK TP (keepThrough ρ m keepρ preserve)
  simpa only [Term.relabel_relabel] using report

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTape
