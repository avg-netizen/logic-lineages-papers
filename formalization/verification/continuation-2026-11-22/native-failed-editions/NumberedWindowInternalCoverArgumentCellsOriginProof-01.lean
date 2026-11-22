module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOriginProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalCoverAscendingRangeOriginDataProof (nilHit)
open NumberedWindowInternalCoverCartesianFoldOriginTargets (blockHit)
open NumberedWindowInternalCoverCartesianFoldOriginChecks (exact_OpenCartesianFoldOrigin)
open NumberedWindowInternalCoverCartesianFoldOriginWitnessProof (blockMemberOfHit)
open NumberedWindowInternalCoverNamedLeafOriginBindingProof (cartesianCases)
open NumberedWindowInternalCoverArgumentCellsTargets
open NumberedWindowInternalCoverArgumentCellsOpenDataProof
open NumberedWindowInternalCoverArgumentCellsBindingProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem singletonKey (one key q a : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph one (rawCons q a) z)))
    (hit : Nonempty (Derivation body Γ (memberGraph one key))) :
    Nonempty (Derivation body Γ (eqn (rawCons q a) key)) := by
  let n := rawCons q a
  obtain ⟨split⟩ := consInversion one n z key cell hit
  let H := (missGraph n key).not
  let T := memberGraph z key
  obtain ⟨same⟩ := nonzeroEquality (body := body) (Γ := H :: Γ) n key
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨bottom⟩ := nilHit (body := body) (Γ := T :: Γ) key
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction same)
    (Derivation.implicationIntroduction (Derivation.explosion bottom))⟩

private theorem atArg (ts ars key q a : OTerm α)
    (hq : Nonempty (Derivation body Γ (memberGraph ts q)))
    (ha : Nonempty (Derivation body Γ (memberGraph ars a)))
    (fromSingleton : Nonempty (Derivation body Γ (blockHit cellSingle a key ![q]))) :
    Nonempty (Derivation body Γ (cellPairOrigin ts ars key)) := by
  apply programCases cellSingle ![a,q] _
  intro β j Δ one keep run
  rw [pairRename]
  simp only [binaryInputsRename] at run
  have hq' := renameInto hq j Δ keep
  have ha' := renameInto ha j Δ keep
  rw [graphRename] at hq' ha'
  have hit := renameInto fromSingleton j Δ keep
  simp only [blockHit,programRename,consTermRename,unaryTapeRename,sucRelabel,zRelabel] at hit
  have actualHit := blockMemberOfHit cellSingle (a.relabel j) (key.relabel j) one ![q.relabel j] run hit
  have cell := singletonCell one (q.relabel j) (a.relabel j) run
  obtain ⟨same⟩ := singletonKey one (key.relabel j) (q.relabel j) (a.relabel j) cell actualHit
  obtain ⟨hq'⟩ := hq'
  obtain ⟨ha'⟩ := ha'
  exact introduce (ts.relabel j) (ars.relabel j) (key.relabel j) (q.relabel j) (a.relabel j)
    ⟨Derivation.conjunctionIntroduction hq' (Derivation.conjunctionIntroduction ha' same)⟩

private theorem atTerm (ts ars key q : OTerm α)
    (hq : Nonempty (Derivation body Γ (memberGraph ts q)))
    (fromRow : Nonempty (Derivation body Γ (blockHit cellBlock q key ![ars]))) :
    Nonempty (Derivation body Γ (cellPairOrigin ts ars key)) := by
  apply programCases cellBlock ![q,ars] _
  intro β j Δ row keep run
  rw [pairRename]
  simp only [binaryInputsRename] at run
  have hq' := renameInto hq j Δ keep
  rw [graphRename] at hq'
  have hit := renameInto fromRow j Δ keep
  simp only [blockHit,programRename,consTermRename,unaryTapeRename,sucRelabel,zRelabel] at hit
  let t := ts.relabel j
  let s := ars.relabel j
  let k := key.relabel j
  let x := q.relabel j
  have actualHit := blockMemberOfHit cellBlock x k row ![s] run hit
  have actualFold := innerGraph row x s run
  have found := exact_OpenCartesianFoldOrigin cellSingle body β Δ s k row ![x] actualFold actualHit
  apply cartesianCases cellSingle s k ![x] _ found
  intro γ l Θ a preserve w
  rw [pairRename]
  have hq'' := renameInto hq' l Θ preserve
  rw [graphRename] at hq''
  rw [unaryTapeRename] at w
  obtain ⟨w⟩ := w
  exact atArg (t.relabel l) (s.relabel l) (k.relabel l) (x.relabel l) a hq''
    ⟨Derivation.conjunctionLeft w⟩ ⟨Derivation.conjunctionRight w⟩

private theorem tailOrigin (trail ts ars key : OTerm α)
    (folded : Nonempty (Derivation body Γ (programGraph cellsTail trail ![ts,ars])))
    (hit : Nonempty (Derivation body Γ (memberGraph trail key))) :
    Nonempty (Derivation body Γ (cellPairOrigin ts ars key)) := by
  have run := outerGraph trail ts ars folded
  have found := exact_OpenCartesianFoldOrigin cellBlock body α Γ ts key trail ![ars] run hit
  apply cartesianCases cellBlock ts key ![ars] _ found
  intro β j Δ q keep w
  rw [pairRename]
  rw [unaryTapeRename] at w
  obtain ⟨w⟩ := w
  exact atTerm (ts.relabel j) (ars.relabel j) (key.relabel j) q
    ⟨Derivation.conjunctionLeft w⟩ ⟨Derivation.conjunctionRight w⟩

private theorem matchOut (out trail ts ars key : OTerm α)
    (whole : Nonempty (Derivation body Γ (cellsReport out ts ars)))
    (folded : Nonempty (Derivation body Γ (programGraph cellsTail trail ![ts,ars])))
    (hit : Nonempty (Derivation body Γ (memberGraph out key))) :
    Nonempty (Derivation body Γ (cellOrigin ts ars key)) := by
  have cell := sentinelCell out trail ts ars whole folded
  obtain ⟨split⟩ := consInversion out z trail key cell hit
  let H := (missGraph z key).not
  let T := memberGraph trail key
  obtain ⟨zeroKey⟩ := nonzeroEquality (body := body) (Γ := H :: Γ) z key
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨paired⟩ := tailOrigin (body := body) (Γ := T :: Γ) trail ts ars key (withHyp folded T)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction (orLeft zeroKey))
    (Derivation.implicationIntroduction (orRight paired))⟩

theorem exact_OpenCoverArgumentCellsOrigin : ExactOpenCoverArgumentCellsOrigin := by
  intro body α Γ out ts ars key whole hit
  apply programCases cellsTail ![ts,ars] _
  intro β j Δ trail keep folded
  rw [originRename]
  simp only [binaryInputsRename] at folded
  have whole' := renameInto whole j Δ keep
  simp only [cellsReport,programRename,binaryInputsRename] at whole'
  have hit' := renameInto hit j Δ keep
  rw [graphRename] at hit'
  exact matchOut (out.relabel j) trail (ts.relabel j) (ars.relabel j) (key.relabel j) whole' folded hit'

#print axioms exact_OpenCoverArgumentCellsOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOriginProof
