module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue successorValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap flatGraph)
open NumberedWindowInternalCoverCartesianFoldOriginChecks (exact_OpenCartesianFoldOrigin)
open NumberedWindowInternalCoverCartesianFoldOriginWitnessProof (blockMemberOfHit)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange rangeReport)
open NumberedWindowInternalCoverAscendingRangeOriginChecks (exact_OpenCoverAscendingRangeOrigin)
open NumberedWindowInternalCoverNamedLeavesTargets
open NumberedWindowInternalCoverNamedLeafOriginTargets
open NumberedWindowInternalCoverNamedLeafOriginBindingProof (cartesianCases introduce namedOriginRename)
open NumberedWindowInternalCoverNamedLeafOriginDataProof (singletonOrigin)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem rangeRename {β : Type} (ids m : OTerm α) (j : α → β) :
    (rangeReport ids (suc m)).relabel j = rangeReport (ids.relabel j) (suc (m.relabel j)) := by
  simp only [rangeReport,programRename,unaryInputsRename,sucRelabel]

private theorem selectedIndex (b : Bool) (K m key ty ids i : OTerm α)
    (typeHit : Nonempty (Derivation body Γ (memberGraph K ty)))
    (indexHit : Nonempty (Derivation body Γ (memberGraph ids i)))
    (leafHit : Nonempty (Derivation body Γ
      (NumberedWindowInternalCoverCartesianFoldOriginTargets.blockHit (singletonLeaf b.toNat) i key ![ty])))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc m)))) :
    Nonempty (Derivation body Γ (namedOrigin b K m key)) := by
  obtain ⟨typeHit⟩ := typeHit
  obtain ⟨bound⟩ := exact_OpenCoverAscendingRangeOrigin body α Γ ids (suc m) i range indexHit
  apply programCases (singletonLeaf b.toNat) ![i,ty] _
  intro β j Δ one keep actual
  rw [namedOriginRename]
  simp only [binaryInputsRename] at actual
  have ht := renameInto (Nonempty.intro typeHit) j Δ keep
  have guard := renameInto (Nonempty.intro bound) j Δ keep
  have hit := renameInto leafHit j Δ keep
  rw [graphRename] at ht
  rw [ID1Completion.InternalOriginalOrderSyntaxProof.orderRename,sucRelabel] at guard
  simp only [NumberedWindowInternalCoverCartesianFoldOriginTargets.blockHit,programRename,
    ID1Completion.InternalRecursionGraphStepSyntaxProof.consTermRename,unaryInputsRename,sucRelabel,
    ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at hit
  have cellHit := blockMemberOfHit (singletonLeaf b.toNat) (i.relabel j) (key.relabel j) one
    ![ty.relabel j] actual hit
  obtain ⟨same⟩ := singletonOrigin b.toNat (ty.relabel j) (i.relabel j) one (key.relabel j) actual cellHit
  obtain ⟨ht⟩ := ht
  obtain ⟨guard⟩ := guard
  exact introduce b (K.relabel j) (m.relabel j) (key.relabel j) (ty.relabel j) (i.relabel j)
    ⟨Derivation.conjunctionIntroduction ht (Derivation.conjunctionIntroduction guard same)⟩

private theorem innerAxis (b : Bool) (K m key ty ids block : OTerm α)
    (typeHit : Nonempty (Derivation body Γ (memberGraph K ty)))
    (run : Nonempty (Derivation body Γ (programGraph (typeBlock b.toNat) block ![ty,ids])))
    (hit : Nonempty (Derivation body Γ (memberGraph block key)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc m)))) :
    Nonempty (Derivation body Γ (namedOrigin b K m key)) := by
  let D := singletonLeaf b.toNat
  have inner : Nonempty (Derivation body Γ (flatGraph D block ids ![ty])) := by
    have h := recoverReordered (flatMap D) (![1,0] : Fin 2 → Fin 2) block ![ty,ids] run
    have tape : (fun j => (![ty,ids] : Fin 2 → OTerm α) ((![1,0] : Fin 2 → Fin 2) j)) =
        Fin.cons ids ![ty] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [tape] at h
    exact h
  have found := exact_OpenCartesianFoldOrigin D body α Γ ids key block ![ty] inner hit
  apply cartesianCases D ids key ![ty] _ found
  intro β j Δ i keep witness
  rw [namedOriginRename]
  have ht := renameInto typeHit j Δ keep
  have bound := renameInto range j Δ keep
  rw [graphRename] at ht
  rw [rangeRename] at bound
  obtain ⟨witness⟩ := witness
  exact selectedIndex b (K.relabel j) (m.relabel j) (key.relabel j) (ty.relabel j)
    (ids.relabel j) i ht ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩ bound

private theorem outerAxis (b : Bool) (K m key ty ids : OTerm α)
    (typeHit : Nonempty (Derivation body Γ (memberGraph K ty)))
    (blockHit : Nonempty (Derivation body Γ
      (NumberedWindowInternalCoverCartesianFoldOriginTargets.blockHit (typeBlock b.toNat) ty key ![ids])))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc m)))) :
    Nonempty (Derivation body Γ (namedOrigin b K m key)) := by
  let D := typeBlock b.toNat
  apply programCases D ![ty,ids] _
  intro β j Δ block keep actual
  rw [namedOriginRename]
  simp only [binaryInputsRename] at actual
  have ht := renameInto typeHit j Δ keep
  have r := renameInto range j Δ keep
  have hit := renameInto blockHit j Δ keep
  rw [graphRename] at ht
  rw [rangeRename] at r
  simp only [NumberedWindowInternalCoverCartesianFoldOriginTargets.blockHit,programRename,
    ID1Completion.InternalRecursionGraphStepSyntaxProof.consTermRename,unaryInputsRename,sucRelabel,
    ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at hit
  have actualHit := blockMemberOfHit D (ty.relabel j) (key.relabel j) block ![ids.relabel j] actual hit
  exact innerAxis b (K.relabel j) (m.relabel j) (key.relabel j) (ty.relabel j) (ids.relabel j)
    block ht actual actualHit r

private theorem actualIds (K m ids : OTerm α)
    (run : Nonempty (Derivation body Γ (rangeReport ids (suc m)))) :
    Nonempty (Derivation body Γ (programGraph idsAt ids ![K,m])) := by
  let xs : Fin 2 → OTerm α := ![K,m]
  have next : Nonempty (Derivation body Γ (programGraph boundSuccessor (suc m) xs)) := by
    apply compositionValue (.succ : Program 1) (fun _ : Fin 1 => .projection 1)
      (suc m) xs ![m] (successorValue ![m])
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  apply compositionValue ascendingRange (fun _ : Fin 1 => boundSuccessor) ids xs ![suc m] run
  intro i
  obtain rfl := Fin.eq_zero i
  exact next

private theorem fromRange (b : Bool) (out K m key ids : OTerm α)
    (named : Nonempty (Derivation body Γ (namedReport b out K m)))
    (hit : Nonempty (Derivation body Γ (memberGraph out key)))
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc m)))) :
    Nonempty (Derivation body Γ (namedOrigin b K m key)) := by
  let xs : Fin 2 → OTerm α := ![K,m]
  let D := typeBlock b.toNat
  have folded : Nonempty (Derivation body Γ (flatGraph D out K ![ids])) := by
    apply compositionRecover (namedFromIds b.toNat)
      (Fin.cons (.projection 0) (Fin.cons idsAt Fin.elim0)) out xs ![K,ids] named
    intro j
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (actualIds K m ids range) (fun k => Fin.elim0 k)) j
  have found := exact_OpenCartesianFoldOrigin D body α Γ K key out ![ids] folded hit
  apply cartesianCases D K key ![ids] _ found
  intro β j Δ ty keep witness
  rw [namedOriginRename]
  have actual := renameInto range j Δ keep
  rw [rangeRename] at actual
  obtain ⟨witness⟩ := witness
  exact outerAxis b (K.relabel j) (m.relabel j) (key.relabel j) ty (ids.relabel j)
    ⟨Derivation.conjunctionLeft witness⟩ ⟨Derivation.conjunctionRight witness⟩ actual

theorem exact_OpenCoverNamedLeafOrigin : ExactOpenCoverNamedLeafOrigin := by
  intro b body α Γ out K m key named hit
  apply programCases ascendingRange ![suc m] _
  intro β j Δ ids keep actual
  rw [namedOriginRename]
  simp only [unaryInputsRename,sucRelabel] at actual
  have named' := renameInto named j Δ keep
  have hit' := renameInto hit j Δ keep
  simp only [namedReport,programRename,binaryInputsRename] at named'
  rw [graphRename] at hit'
  exact fromRange b (out.relabel j) (K.relabel j) (m.relabel j) (key.relabel j) ids named' hit' actual

#print axioms exact_OpenCoverNamedLeafOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginChecks
