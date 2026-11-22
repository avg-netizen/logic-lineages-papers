module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldThinOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsConstructorProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalCoverCartesianFoldTargets (flatGraph)
open NumberedWindowInternalCoverCartesianFoldSyntaxProof (flatRename)
open NumberedWindowInternalCoverCartesianFoldThinOpenProof (exact_OpenCartesianFoldMember)
open NumberedWindowInternalCoverArgumentCellsTargets
open NumberedWindowInternalCoverArgumentCellsOpenDataProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem sentinel (out ts ars : OTerm α)
    (whole : Nonempty (Derivation body Γ (cellsReport out ts ars))) :
    Nonempty (Derivation body Γ (memberGraph out z)) := by
  apply programCases cellsTail ![ts,ars] _
  intro β j Δ trail keep flat
  rw [graphRename,zRelabel]
  simp only [binaryInputsRename] at flat
  have whole' := renameInto whole j Δ keep
  simp only [cellsReport,programRename,binaryInputsRename] at whole'
  let o := out.relabel j
  have cell := sentinelCell o trail (ts.relabel j) (ars.relabel j) whole' flat
  exact headMember o z trail z cell ⟨refl z⟩

private theorem innerHit (row q a ars : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph cellSingle row ars ![q])))
    (ha : Nonempty (Derivation body Γ (memberGraph ars a))) :
    Nonempty (Derivation body Γ (memberGraph row (rawCons q a))) := by
  apply programCases cellSingle ![a,q] _
  intro β j Δ one keep singleton
  rw [graphRename,rawConsRename]
  simp only [binaryInputsRename] at singleton
  have run' := renameInto run j Δ keep
  rw [flatRename,unaryTapeRename] at run'
  have ha' := renameInto ha j Δ keep
  rw [graphRename] at ha'
  let key := rawCons (q.relabel j) (a.relabel j)
  have actual := singletonCell one (q.relabel j) (a.relabel j) singleton
  have oneHit := headMember one key z key actual ⟨refl key⟩
  exact exact_OpenCartesianFoldMember cellSingle body β Δ (ars.relabel j) (a.relabel j) one key
    (row.relabel j) ![q.relabel j] ha' singleton oneHit run'

private theorem tailHit (trail ts ars q a : OTerm α)
    (run : Nonempty (Derivation body Γ (flatGraph cellBlock trail ts ![ars])))
    (hq : Nonempty (Derivation body Γ (memberGraph ts q)))
    (ha : Nonempty (Derivation body Γ (memberGraph ars a))) :
    Nonempty (Derivation body Γ (memberGraph trail (rawCons q a))) := by
  apply programCases cellBlock ![q,ars] _
  intro β j Δ row keep rowRun
  rw [graphRename,rawConsRename]
  simp only [binaryInputsRename] at rowRun
  have run' := renameInto run j Δ keep
  rw [flatRename,unaryTapeRename] at run'
  have hq' := renameInto hq j Δ keep
  have ha' := renameInto ha j Δ keep
  rw [graphRename] at hq' ha'
  let key := rawCons (q.relabel j) (a.relabel j)
  have actual := innerGraph row (q.relabel j) (ars.relabel j) rowRun
  have hit := innerHit row (q.relabel j) (a.relabel j) (ars.relabel j) actual ha'
  exact exact_OpenCartesianFoldMember cellBlock body β Δ (ts.relabel j) (q.relabel j) row key
    (trail.relabel j) ![ars.relabel j] hq' rowRun hit run'

theorem paired (out ts ars q a : OTerm α)
    (whole : Nonempty (Derivation body Γ (cellsReport out ts ars)))
    (hq : Nonempty (Derivation body Γ (memberGraph ts q)))
    (ha : Nonempty (Derivation body Γ (memberGraph ars a))) :
    Nonempty (Derivation body Γ (memberGraph out (rawCons q a))) := by
  apply programCases cellsTail ![ts,ars] _
  intro β j Δ trail keep flat
  rw [graphRename,rawConsRename]
  simp only [binaryInputsRename] at flat
  have whole' := renameInto whole j Δ keep
  simp only [cellsReport,programRename,binaryInputsRename] at whole'
  have hq' := renameInto hq j Δ keep
  have ha' := renameInto ha j Δ keep
  simp only [graphRename] at hq' ha'
  let o := out.relabel j
  let t := ts.relabel j
  let s := ars.relabel j
  have cell := sentinelCell o trail t s whole' flat
  have h := tailHit trail t s (q.relabel j) (a.relabel j) (outerGraph trail t s flat) hq' ha'
  exact tailMember o z trail (rawCons (q.relabel j) (a.relabel j)) cell h

theorem exact_OpenCoverArgumentCellsConstructor : ExactOpenCoverArgumentCellsConstructor := by
  intro body α Γ out ts ars q a run
  exact ⟨sentinel out ts ars run, paired out ts ars q a run⟩

#print axioms exact_OpenCoverArgumentCellsConstructor

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsConstructorProof
