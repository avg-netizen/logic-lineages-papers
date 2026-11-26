module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedKeptToTargetProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSourceBalanceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedOriginCasesRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedPartitionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSharedTypedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCertifiedUnionStepProof (Pr SplitCases unionGraph)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalLiteralTypedPartitionProof (Typed exact_LiteralTypedParts)
open NumberedWindowInternalRawUnionFromEquivalentPartsProof (Cmp)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverSymmetry exact_LiteralObserverTransitivity)
open NumberedWindowInternalCertifiedKeptToTargetProof (Before exact_OriginalCertifiedKeptToTarget)
open NumberedWindowInternalCertifiedSourceBalanceProof (exact_OriginalCertifiedSourceBalance)
open NumberedWindowInternalCertifiedOriginCasesRenameProof (exact_OriginalSplitCasesRelabel)
open NumberedWindowInternalChangedSideFromScratchProof (Body)

attribute [local irreducible] programGraph
variable {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem moveShared (i : Program 1) (r : Program 3) (c : Nat)
    {u v rawK rawD rawA s t k d a p sk tp : OTerm α}
    (run : Reports permutation permutation r (Body i r c) Γ u v rawK rawD rawA s t k d a p sk tp)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Reports permutation permutation r (Body i r c) Δ (u.relabel j) (v.relabel j) (rawK.relabel j)
      (rawD.relabel j) (rawA.relabel j) (s.relabel j) (t.relabel j) (k.relabel j) (d.relabel j)
      (a.relabel j) (p.relabel j) (sk.relabel j) (tp.relabel j) := by
  constructor
  · exact renameParser u s run.sourceParsed j Δ keep
  · exact renameParser v t run.targetParsed j Δ keep
  · exact renameParser rawK k run.keptParsed j Δ keep
  · exact renameParser rawD d run.removedParsed j Δ keep
  · exact renameParser rawA a run.insertedParsed j Δ keep
  · simpa only [unaryRename,sucRelabel] using renameInto run.rawProjection j Δ keep
  · simpa only [unaryRename,sucRelabel] using renameInto run.scratchProjection j Δ keep
  · exact renamePair append sk k d run.sourceAppend j keep
  · exact renamePair append tp k p run.targetAppend j keep
  · simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) s sk run.sourceObserved j keep
  · simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) t tp run.targetObserved j keep
  · simpa only [loopRename] using renameInto run.scanObserved j Δ keep

theorem moveTyped (i : Program 1) (r : Program 3) (c : Nat) (s : OTerm α)
    (report : Pr (literalData i r) c Γ (Typed i s))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Pr (literalData i r) c Δ (Typed i (s.relabel j)) := by
  simpa only [Typed,unaryRename,sucRelabel,zRelabel] using renameInto report j Δ keep

/-- With actual same-tape source/target typing and actual removed cons
from the original boundary, align the original union input to the actual
certificate's kept/removed source and finish the genuine split. -/
theorem exact_OriginalCertifiedFromTypedShared (i : Program 1) (r : Program 3) (c : Nat)
    (a b u v rawK rawD rawA s t k d rows p sk tp dh dTail : OTerm α)
    (goal : Formula α)
    (run : Reports permutation permutation r (Body i r c) Γ u v rawK rawD rawA s t k d rows p sk tp)
    (admitS : Pr (literalData i r) c Γ (Typed i s))
    (admitT : Pr (literalData i r) c Γ (Typed i t))
    (removed : Pr (literalData i r) c Γ (consGraph d dh dTail))
    (joint : Pr (literalData i r) c Γ (unionGraph permutation a b u))
    (next : SplitCases (literalData i r) c permutation Γ a b v goal) :
    Pr (literalData i r) c Γ goal := by
  let B := Body i r c
  apply exact_OriginalCertifiedSourceBalance a b u s sk goal joint run.sourceParsed run.sourceObserved
  intro β j Δ ls rs join keep parseL parseR app bal
  have rr := moveShared i r c run j keep
  have leftCount : Nonempty (Derivation B Δ (Cmp (s.relabel j) join)) :=
    exact_LiteralObserverTransitivity (s.relabel j) (sk.relabel j) join rr.sourceObserved
      (exact_LiteralObserverSymmetry join (sk.relabel j) bal)
  obtain ⟨li,ri⟩ := exact_LiteralTypedParts i (s.relabel j) ls rs join
    (moveTyped i r c s admitS j keep) app leftCount
  have cell := renameInto removed j Δ keep
  rw [consGraphRename] at cell
  have mvT := moveTyped i r c t admitT j keep
  have p0 : Before i r c Δ (a.relabel j) (b.relabel j) (v.relabel j) ls rs (t.relabel j)
      (k.relabel j) (d.relabel j) (dh.relabel j) (dTail.relabel j) (rawD.relabel j) (p.relabel j)
      (rows.relabel j) (tp.relabel j) :=
    ⟨parseL,parseR,rr.targetParsed,li,ri,mvT,cell,rr.removedParsed,rr.scanObserved,
      rr.scratchProjection,rr.targetAppend,rr.targetObserved⟩
  exact exact_OriginalCertifiedKeptToTarget i r c (a.relabel j) (b.relabel j) (v.relabel j)
    ls rs (t.relabel j) (k.relabel j) (d.relabel j) (dh.relabel j) (dTail.relabel j)
    (rawD.relabel j) (p.relabel j) (rows.relabel j) (tp.relabel j) join (sk.relabel j)
    (goal.relabel j) p0 app rr.sourceAppend bal
    (exact_OriginalSplitCasesRelabel (literalData i r) c permutation a b v goal next j keep)

#print axioms exact_OriginalCertifiedFromTypedShared
end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSharedTypedProof
