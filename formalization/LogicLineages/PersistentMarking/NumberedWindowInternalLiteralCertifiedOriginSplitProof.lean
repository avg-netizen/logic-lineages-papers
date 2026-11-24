module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSharedTypedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryAtSharedTapesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedOriginCasesRenameProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCertifiedOriginSplitProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCertifiedUnionStepProof (Pr SplitCases CertifiedOriginSplit unionGraph)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (unionGraphRename)
open NumberedWindowInternalDirectCoreInstalledCertificateProof (exact_InstalledCertificateSharedTape)
open NumberedWindowInternalDirectBoundaryAtSharedTapesProof (exact_OpenBoundaryAtSharedTapes)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalDirectBoundaryGuardsTargets (boundaryRaw)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalChangedSideFromScratchProof (Body)
open NumberedWindowInternalCertifiedSharedTypedProof (moveShared exact_OriginalCertifiedFromTypedShared)
open NumberedWindowInternalCertifiedOriginCasesRenameProof (exact_OriginalSplitCasesRelabel)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

theorem exact_OriginalCertifiedFromShared (i : Program 1) (r : Program 3) (c : Nat)
    (a b u v rawK rawD rawA s t k d rows p sk tp : OTerm α) (goal : Formula α)
    (run : Reports permutation permutation r (Body i r c) Γ u v rawK rawD rawA s t k d rows p sk tp)
    (bd : Pr (literalData i r) c Γ (programGraph (boundaryRaw i) (suc z) (sourceTape u v rawD)))
    (joint : Pr (literalData i r) c Γ (unionGraph permutation a b u))
    (next : SplitCases (literalData i r) c permutation Γ a b v goal) :
    Pr (literalData i r) c Γ goal := by
  apply exact_OpenBoundaryAtSharedTapes i u v rawD s t d
    ⟨run.sourceParsed,run.targetParsed,run.removedParsed⟩ bd goal
  intro β j Δ dh dt keep hs ht cell
  have identical := moveShared i r c run j keep
  have join := renameInto joint j Δ keep
  rw [unionGraphRename] at join
  exact exact_OriginalCertifiedFromTypedShared i r c (a.relabel j) (b.relabel j) (u.relabel j) (v.relabel j)
    (rawK.relabel j) (rawD.relabel j) (rawA.relabel j) (s.relabel j) (t.relabel j) (k.relabel j)
    (d.relabel j) (rows.relabel j) (p.relabel j) (sk.relabel j) (tp.relabel j) dh dt
    (goal.relabel j) identical hs ht cell join
    (exact_OriginalSplitCasesRelabel (literalData i r) c permutation a b v goal next j keep)

/-- The actual fresh original odd certificate is split in the literal
jRaw/dCore body. The same original unchanged raw term is kept on either
empty side, and every strict side is proved by a real tag-5 certificate
at the exact packed destination. The held union of the actual destination
is rebuilt in each case. No extra count, typing or split premise. -/
theorem exact_LiteralCertifiedOriginSplit (i : Program 1) (r : Program 3) (c : Nat) :
    CertifiedOriginSplit (literalData i r) c permutation := by
  intro α Γ a b u v w goal _carrier joint certified next
  apply exact_InstalledCertificateSharedTape i (jRaw i) r permutation c α Γ u w v goal certified
  intro β j Δ rawK rawD rawA s t k d rows p sk tp keep _env _pack bd run
  have join := renameInto joint j Δ keep
  rw [unionGraphRename] at join
  exact exact_OriginalCertifiedFromShared i r c (a.relabel j) (b.relabel j) (u.relabel j) (v.relabel j)
    rawK rawD rawA s t k d rows p sk tp (goal.relabel j) run bd join
    (exact_OriginalSplitCasesRelabel (literalData i r) c permutation a b v goal next j keep)

#print axioms exact_OriginalCertifiedFromShared
#print axioms exact_LiteralCertifiedOriginSplit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCertifiedOriginSplitProof
