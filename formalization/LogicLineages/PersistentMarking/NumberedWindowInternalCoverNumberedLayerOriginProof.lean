module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOriginProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z zRelabel sucRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalCoverAscendingRangeOriginDataProof (nilHit)
open NumberedWindowInternalCoverCartesianFoldTargets (flatGraph)
open NumberedWindowInternalCoverCartesianFoldOriginTargets (blockHit)
open NumberedWindowInternalCoverCartesianFoldOriginChecks (exact_OpenCartesianFoldOrigin)
open NumberedWindowInternalCoverCartesianFoldOriginWitnessProof (blockMemberOfHit)
open NumberedWindowInternalCoverNamedLeafOriginBindingProof (cartesianCases)
open NumberedWindowInternalCoverNumberedLayerTargets
open NumberedWindowInternalCoverNumberedLayerOpenDataProof
open NumberedWindowInternalCoverNumberedLayerBindingProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- This equality is recovered from the actual standard singleton, not by
numeric reassessment of the observed sparse key. -/
private theorem singletonKey (one h ty k l r key : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph one (numberedTerm h ty k l r) z)))
    (hit : Nonempty (Derivation body Γ (memberGraph one key))) :
    Nonempty (Derivation body Γ (eqn (numberedTerm h ty k l r) key)) := by
  let n := numberedTerm h ty k l r
  obtain ⟨split⟩ := consInversion one n z key cell hit
  let P := (missGraph n key).not
  let T := memberGraph z key
  obtain ⟨same⟩ := nonzeroEquality (body := body) (Γ := P :: Γ) n key
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨bottom⟩ := nilHit (body := body) (Γ := T :: Γ) key
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction same)
    (Derivation.implicationIntroduction (Derivation.explosion bottom))⟩

private theorem selectedSuffix (H K ids args key h ty k l r : OTerm α)
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hk : Nonempty (Derivation body Γ (memberGraph ids k)))
    (hl : Nonempty (Derivation body Γ (memberGraph args l)))
    (hr : Nonempty (Derivation body Γ (memberGraph args r)))
    (blockIn : Nonempty (Derivation body Γ (blockHit singletonNumbered r key ![h,ty,k,l]))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  apply programCases singletonNumbered ![r,h,ty,k,l] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [quintInputsRename] at row
  have hh' := renameInto hh j Δ keep
  have ht' := renameInto ht j Δ keep
  have hk' := renameInto hk j Δ keep
  have hl' := renameInto hl j Δ keep
  have hr' := renameInto hr j Δ keep
  simp only [graphRename] at hh' ht' hk' hl' hr'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,quadInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit singletonNumbered (r.relabel j) (key.relabel j) block
    ![h.relabel j,ty.relabel j,k.relabel j,l.relabel j] row checked
  have cell := singletonCell block (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) row
  obtain ⟨same⟩ := singletonKey block (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) (key.relabel j) cell inBlock
  obtain ⟨hh'⟩ := hh'
  obtain ⟨ht'⟩ := ht'
  obtain ⟨hk'⟩ := hk'
  obtain ⟨hl'⟩ := hl'
  obtain ⟨hr'⟩ := hr'
  exact introduce (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j)
    ⟨Derivation.conjunctionIntroduction hh' (Derivation.conjunctionIntroduction ht'
      (Derivation.conjunctionIntroduction hk' (Derivation.conjunctionIntroduction hl'
        (Derivation.conjunctionIntroduction hr' same))))⟩

private theorem recoverSuffix (out H K ids args key h ty k l : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph singletonNumbered out args ![h,ty,k,l])))
    (image : Nonempty (Derivation body Γ (memberGraph out key)))
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hk : Nonempty (Derivation body Γ (memberGraph ids k)))
    (hl : Nonempty (Derivation body Γ (memberGraph args l))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  have found := exact_OpenCartesianFoldOrigin singletonNumbered body α Γ args key out ![h,ty,k,l] actual image
  apply cartesianCases singletonNumbered args key ![h,ty,k,l] _ found
  intro β j Δ r keep witness
  rw [originRename]
  rw [quadInputsRename] at witness
  have hh' := renameInto hh j Δ keep
  have ht' := renameInto ht j Δ keep
  have hk' := renameInto hk j Δ keep
  have hl' := renameInto hl j Δ keep
  simp only [graphRename] at hh' ht' hk' hl'
  obtain ⟨witness⟩ := witness
  exact selectedSuffix (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) r
    hh' ht' hk' hl' ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

private theorem selectedPrefix (H K ids args key h ty k l : OTerm α)
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hk : Nonempty (Derivation body Γ (memberGraph ids k)))
    (hl : Nonempty (Derivation body Γ (memberGraph args l)))
    (blockIn : Nonempty (Derivation body Γ (blockHit prefixBlock l key ![args,h,ty,k]))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  apply programCases prefixBlock ![l,args,h,ty,k] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [quintInputsRename] at row
  have hh' := renameInto hh j Δ keep
  have ht' := renameInto ht j Δ keep
  have hk' := renameInto hk j Δ keep
  have hl' := renameInto hl j Δ keep
  simp only [graphRename] at hh' ht' hk' hl'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,quadInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit prefixBlock (l.relabel j) (key.relabel j) block
    ![args.relabel j,h.relabel j,ty.relabel j,k.relabel j] row checked
  have inner := fromPrefix block (l.relabel j) (args.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) row
  exact recoverSuffix block (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j)
    inner inBlock hh' ht' hk' hl'

private theorem recoverPrefix (out H K ids args key h ty k : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph prefixBlock out args ![args,h,ty,k])))
    (image : Nonempty (Derivation body Γ (memberGraph out key)))
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hk : Nonempty (Derivation body Γ (memberGraph ids k))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  have found := exact_OpenCartesianFoldOrigin prefixBlock body α Γ args key out ![args,h,ty,k] actual image
  apply cartesianCases prefixBlock args key ![args,h,ty,k] _ found
  intro β j Δ l keep witness
  rw [originRename]
  rw [quadInputsRename] at witness
  have hh' := renameInto hh j Δ keep
  have ht' := renameInto ht j Δ keep
  have hk' := renameInto hk j Δ keep
  simp only [graphRename] at hh' ht' hk'
  obtain ⟨witness⟩ := witness
  exact selectedPrefix (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) l
    hh' ht' hk' ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

private theorem selectedId (H K ids args key h ty k : OTerm α)
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hk : Nonempty (Derivation body Γ (memberGraph ids k)))
    (blockIn : Nonempty (Derivation body Γ (blockHit idBlock k key ![args,h,ty]))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  apply programCases idBlock ![k,args,h,ty] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [quadInputsRename] at row
  have hh' := renameInto hh j Δ keep
  have ht' := renameInto ht j Δ keep
  have hk' := renameInto hk j Δ keep
  simp only [graphRename] at hh' ht' hk'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,tripleInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit idBlock (k.relabel j) (key.relabel j) block
    ![args.relabel j,h.relabel j,ty.relabel j] row checked
  have inner := fromId block (k.relabel j) (args.relabel j) (h.relabel j) (ty.relabel j) row
  exact recoverPrefix block (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j)
    inner inBlock hh' ht' hk'

private theorem recoverId (out H K ids args key h ty : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph idBlock out ids ![args,h,ty])))
    (image : Nonempty (Derivation body Γ (memberGraph out key)))
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  have found := exact_OpenCartesianFoldOrigin idBlock body α Γ ids key out ![args,h,ty] actual image
  apply cartesianCases idBlock ids key ![args,h,ty] _ found
  intro β j Δ k keep witness
  rw [originRename]
  rw [tripleInputsRename] at witness
  have hh' := renameInto hh j Δ keep
  have ht' := renameInto ht j Δ keep
  simp only [graphRename] at hh' ht'
  obtain ⟨witness⟩ := witness
  exact selectedId (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j) (ty.relabel j) k
    hh' ht' ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

private theorem selectedType (H K ids args key h ty : OTerm α)
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (blockIn : Nonempty (Derivation body Γ (blockHit typeBlock ty key ![ids,args,h]))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  apply programCases typeBlock ![ty,ids,args,h] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [quadInputsRename] at row
  have hh' := renameInto hh j Δ keep
  have ht' := renameInto ht j Δ keep
  simp only [graphRename] at hh' ht'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,tripleInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit typeBlock (ty.relabel j) (key.relabel j) block
    ![ids.relabel j,args.relabel j,h.relabel j] row checked
  have inner := fromType block (ty.relabel j) (ids.relabel j) (args.relabel j) (h.relabel j) row
  exact recoverId block (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j) (ty.relabel j)
    inner inBlock hh' ht'

private theorem recoverType (out H K ids args key h : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph typeBlock out K ![ids,args,h])))
    (image : Nonempty (Derivation body Γ (memberGraph out key)))
    (hh : Nonempty (Derivation body Γ (memberGraph H h))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  have found := exact_OpenCartesianFoldOrigin typeBlock body α Γ K key out ![ids,args,h] actual image
  apply cartesianCases typeBlock K key ![ids,args,h] _ found
  intro β j Δ ty keep witness
  rw [originRename]
  rw [tripleInputsRename] at witness
  have hh' := renameInto hh j Δ keep
  simp only [graphRename] at hh'
  obtain ⟨witness⟩ := witness
  exact selectedType (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j) ty
    hh' ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

private theorem selectedHead (H K ids args key h : OTerm α)
    (hh : Nonempty (Derivation body Γ (memberGraph H h)))
    (blockIn : Nonempty (Derivation body Γ (blockHit headBlock h key ![K,ids,args]))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  apply programCases headBlock ![h,K,ids,args] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [quadInputsRename] at row
  have hh' := renameInto hh j Δ keep
  simp only [graphRename] at hh'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,tripleInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit headBlock (h.relabel j) (key.relabel j) block
    ![K.relabel j,ids.relabel j,args.relabel j] row checked
  have inner := fromHead block (h.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) row
  exact recoverType block (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) (h.relabel j)
    inner inBlock hh'

private theorem recoverHead (out H K ids args key : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph headBlock out H ![K,ids,args])))
    (image : Nonempty (Derivation body Γ (memberGraph out key))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  have found := exact_OpenCartesianFoldOrigin headBlock body α Γ H key out ![K,ids,args] actual image
  apply cartesianCases headBlock H key ![K,ids,args] _ found
  intro β j Δ h keep witness
  rw [originRename]
  rw [tripleInputsRename] at witness
  obtain ⟨witness⟩ := witness
  exact selectedHead (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) h
    ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

theorem exact_OpenCoverNumberedLayerOrigin : ExactOpenCoverNumberedLayerOrigin := by
  intro body α Γ out H K ids args key run hit
  exact recoverHead out H K ids args key (outerGraph out H K ids args run) hit

#print axioms exact_OpenCoverNumberedLayerOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerOriginProof
