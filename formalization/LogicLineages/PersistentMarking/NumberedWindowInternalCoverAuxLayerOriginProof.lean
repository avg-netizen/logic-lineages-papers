module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerBindingProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerOriginProof
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
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename quadInputsRename)
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
open NumberedWindowInternalCoverAuxApplicationsTargets
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverAuxLayerTransportTargets
open NumberedWindowInternalCoverAuxLayerOpenDataProof
open NumberedWindowInternalCoverAuxLayerBindingProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- This equality is recovered from the actual standard singleton, not by
numeric reassessment of the observed sparse key. -/
private theorem singletonKey (one d c f a key : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph one (auxiliaryTerm d c f a) z)))
    (hit : Nonempty (Derivation body Γ (memberGraph one key))) :
    Nonempty (Derivation body Γ (eqn (auxiliaryTerm d c f a) key)) := by
  let n := auxiliaryTerm d c f a
  obtain ⟨split⟩ := consInversion one n z key cell hit
  let P := (missGraph n key).not
  let T := memberGraph z key
  obtain ⟨same⟩ := nonzeroEquality (body := body) (Γ := P :: Γ) n key
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨bottom⟩ := nilHit (body := body) (Γ := T :: Γ) key
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction same)
    (Derivation.implicationIntroduction (Derivation.explosion bottom))⟩

private theorem selectedArgument (K T key d c f a : OTerm α)
    (hd : Nonempty (Derivation body Γ (memberGraph K d)))
    (hc : Nonempty (Derivation body Γ (memberGraph K c)))
    (hf : Nonempty (Derivation body Γ (memberGraph T f)))
    (ha : Nonempty (Derivation body Γ (memberGraph T a)))
    (blockIn : Nonempty (Derivation body Γ (blockHit singletonAux a key ![d,c,f]))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  apply programCases singletonAux ![a,d,c,f] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [quadInputsRename] at row
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  have hf' := renameInto hf j Δ keep
  have ha' := renameInto ha j Δ keep
  simp only [graphRename] at hd' hc' hf' ha'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,tripleInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit singletonAux (a.relabel j) (key.relabel j) block
    ![d.relabel j,c.relabel j,f.relabel j] row checked
  have cell := singletonCell block (d.relabel j) (c.relabel j) (f.relabel j) (a.relabel j) row
  obtain ⟨same⟩ := singletonKey block (d.relabel j) (c.relabel j) (f.relabel j) (a.relabel j) (key.relabel j) cell inBlock
  obtain ⟨hd'⟩ := hd'
  obtain ⟨hc'⟩ := hc'
  obtain ⟨hf'⟩ := hf'
  obtain ⟨ha'⟩ := ha'
  exact introduce (K.relabel j) (T.relabel j) (key.relabel j) (d.relabel j) (c.relabel j) (f.relabel j) (a.relabel j)
    ⟨Derivation.conjunctionIntroduction hd' (Derivation.conjunctionIntroduction hc'
      (Derivation.conjunctionIntroduction hf' (Derivation.conjunctionIntroduction ha' same)))⟩

private theorem recoverArgument (out K T key d c f : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph singletonAux out T ![d,c,f])))
    (image : Nonempty (Derivation body Γ (memberGraph out key)))
    (hd : Nonempty (Derivation body Γ (memberGraph K d)))
    (hc : Nonempty (Derivation body Γ (memberGraph K c)))
    (hf : Nonempty (Derivation body Γ (memberGraph T f))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  have found := exact_OpenCartesianFoldOrigin singletonAux body α Γ T key out ![d,c,f] actual image
  apply cartesianCases singletonAux T key ![d,c,f] _ found
  intro β j Δ a keep witness
  rw [originRename]
  rw [tripleInputsRename] at witness
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  have hf' := renameInto hf j Δ keep
  simp only [graphRename] at hd' hc' hf'
  obtain ⟨witness⟩ := witness
  exact selectedArgument (K.relabel j) (T.relabel j) (key.relabel j) (d.relabel j) (c.relabel j) (f.relabel j) a
    hd' hc' hf' ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

private theorem selectedFunction (K T key d c f : OTerm α)
    (hd : Nonempty (Derivation body Γ (memberGraph K d)))
    (hc : Nonempty (Derivation body Γ (memberGraph K c)))
    (hf : Nonempty (Derivation body Γ (memberGraph T f)))
    (blockIn : Nonempty (Derivation body Γ (blockHit argAxis f key ![T,d,c]))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  apply programCases argAxis ![f,T,d,c] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [quadInputsRename] at row
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  have hf' := renameInto hf j Δ keep
  simp only [graphRename] at hd' hc' hf'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,tripleInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit argAxis (f.relabel j) (key.relabel j) block
    ![T.relabel j,d.relabel j,c.relabel j] row checked
  have inner := fromFunction block (f.relabel j) (T.relabel j) (d.relabel j) (c.relabel j) row
  exact recoverArgument block (K.relabel j) (T.relabel j) (key.relabel j) (d.relabel j) (c.relabel j) (f.relabel j)
    inner inBlock hd' hc' hf'

private theorem recoverFunction (out K T key d c : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph argAxis out T ![T,d,c])))
    (image : Nonempty (Derivation body Γ (memberGraph out key)))
    (hd : Nonempty (Derivation body Γ (memberGraph K d)))
    (hc : Nonempty (Derivation body Γ (memberGraph K c))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  have found := exact_OpenCartesianFoldOrigin argAxis body α Γ T key out ![T,d,c] actual image
  apply cartesianCases argAxis T key ![T,d,c] _ found
  intro β j Δ f keep witness
  rw [originRename]
  rw [tripleInputsRename] at witness
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  simp only [graphRename] at hd' hc'
  obtain ⟨witness⟩ := witness
  exact selectedFunction (K.relabel j) (T.relabel j) (key.relabel j) (d.relabel j) (c.relabel j) f
    hd' hc' ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

private theorem selectedCodomain (K T key d c : OTerm α)
    (hd : Nonempty (Derivation body Γ (memberGraph K d)))
    (hc : Nonempty (Derivation body Γ (memberGraph K c)))
    (blockIn : Nonempty (Derivation body Γ (blockHit fnAxis c key ![K,T,d]))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  apply programCases fnAxis ![c,K,T,d] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [quadInputsRename] at row
  have hd' := renameInto hd j Δ keep
  have hc' := renameInto hc j Δ keep
  simp only [graphRename] at hd' hc'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,tripleInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit fnAxis (c.relabel j) (key.relabel j) block
    ![K.relabel j,T.relabel j,d.relabel j] row checked
  have inner := fromCodomain block (c.relabel j) (K.relabel j) (T.relabel j) (d.relabel j) row
  exact recoverFunction block (K.relabel j) (T.relabel j) (key.relabel j) (d.relabel j) (c.relabel j)
    inner inBlock hd' hc'

private theorem recoverCodomain (out K T key d : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph fnAxis out K ![K,T,d])))
    (image : Nonempty (Derivation body Γ (memberGraph out key)))
    (hd : Nonempty (Derivation body Γ (memberGraph K d))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  have found := exact_OpenCartesianFoldOrigin fnAxis body α Γ K key out ![K,T,d] actual image
  apply cartesianCases fnAxis K key ![K,T,d] _ found
  intro β j Δ c keep witness
  rw [originRename]
  rw [tripleInputsRename] at witness
  have hd' := renameInto hd j Δ keep
  simp only [graphRename] at hd'
  obtain ⟨witness⟩ := witness
  exact selectedCodomain (K.relabel j) (T.relabel j) (key.relabel j) (d.relabel j) c
    hd' ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

private theorem selectedDomain (K T key d : OTerm α)
    (hd : Nonempty (Derivation body Γ (memberGraph K d)))
    (blockIn : Nonempty (Derivation body Γ (blockHit codAxis d key ![K,T]))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  apply programCases codAxis ![d,K,T] _
  intro β j Δ block keep row
  rw [originRename]
  simp only [tripleInputsRename] at row
  have hd' := renameInto hd j Δ keep
  simp only [graphRename] at hd'
  have checked := renameInto blockIn j Δ keep
  simp only [blockHit,programRename,consTermRename,binaryInputsRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit codAxis (d.relabel j) (key.relabel j) block
    ![K.relabel j,T.relabel j] row checked
  have inner := fromDomain block (d.relabel j) (K.relabel j) (T.relabel j) row
  exact recoverCodomain block (K.relabel j) (T.relabel j) (key.relabel j) (d.relabel j)
    inner inBlock hd'

private theorem recoverDomain (out K T key : OTerm α)
    (actual : Nonempty (Derivation body Γ (flatGraph codAxis out K ![K,T])))
    (image : Nonempty (Derivation body Γ (memberGraph out key))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  have found := exact_OpenCartesianFoldOrigin codAxis body α Γ K key out ![K,T] actual image
  apply cartesianCases codAxis K key ![K,T] _ found
  intro β j Δ d keep witness
  rw [originRename]
  rw [binaryInputsRename] at witness
  obtain ⟨witness⟩ := witness
  exact selectedDomain (K.relabel j) (T.relabel j) (key.relabel j) d
    ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩

theorem exact_OpenCoverAuxLayerOrigin : ExactOpenCoverAuxLayerOrigin := by
  intro body α Γ out K T key run hit
  exact recoverDomain out K T key (outerGraph out K T run) hit

#print axioms exact_OpenCoverAuxLayerOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerOriginProof
