module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport valueUnique equalEqn)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc sucNeZeroApply)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets targetBase targetStep)
open NumberedWindowInternalDirectTargetMapCons (exactOpenTargetMapCons)
open NumberedWindowInternalDirectTargetMapOriginTargets
open NumberedWindowInternalDirectTargetMapOriginSyntaxProof
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem witness (code key row : OTerm α)
    (h : Derivation B Γ (originRow code key row)) : Nonempty (Derivation B Γ (origin code key)) := by
  refine ⟨Derivation.existentialIntroduction (emb row) ?_⟩
  rw [instantiateRow]
  exact h

theorem useAtOutput (code key out : OTerm α)
    (all : Nonempty (Derivation B Γ (allOutputs code key))) :
    Nonempty (Derivation B Γ (atOutput code key out)) := by
  obtain ⟨h⟩ := all
  have got := Derivation.universalElimination (emb out) h
  rw [instantiateOutput] at got
  exact ⟨got⟩

private theorem liftOrigin (code h tail key : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code h tail)))
    (old : Nonempty (Derivation B Γ (origin tail key))) :
    Nonempty (Derivation B Γ (origin code key)) := by
  obtain ⟨o⟩ := old
  let φ := originBody tail key
  let ρ : α → α ⊕ Fin 1 := Sum.inl
  let Δ := φ :: Γ.map (fun f => f.relabel ρ)
  let row : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have held : Derivation B Δ (originRow (tail.relabel ρ) (key.relabel ρ) row) :=
    Derivation.hypothesis List.mem_cons_self
  have keep : ∀ f ∈ Γ, f.relabel ρ ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have c := renameInto cell ρ Δ keep
  rw [consGraphRename] at c
  have strengthened : Nonempty (Derivation B Δ (origin (code.relabel ρ) (key.relabel ρ))) := by
    obtain ⟨m⟩ := tailMember (code.relabel ρ) (h.relabel ρ) (tail.relabel ρ) row c
      ⟨Derivation.conjunctionLeft held⟩
    exact witness _ _ _ (Derivation.conjunctionIntroduction m (Derivation.conjunctionRight held))
  have relabelled : Nonempty (Derivation B Δ (weaken (origin code key))) := by
    rw [weaken,originRename]
    exact strengthened
  obtain ⟨wrapped⟩ := relabelled
  exact ⟨Derivation.existentialElimination o wrapped⟩

private theorem nilMemberFalse (key : OTerm α)
    (h : Nonempty (Derivation B Γ (memberGraph z key))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  have q := nilRecover memberBase memberStep (suc z) ![key] h
  obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![key] q (constantZeroValue ![key])
  exact ⟨sucNeZeroApply bad⟩

theorem nilAt (key out : OTerm α) : Nonempty (Derivation B Γ (atOutput z key out)) := by
  let H := unary scratchTargets (suc out) z ⊓ memberGraph out key
  have h : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  have q := nilRecover targetBase targetStep (suc out) Fin.elim0 ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨eq⟩ := valueUnique targetBase (suc out) (suc z) Fin.elim0 q (literalGraph 1 Fin.elim0)
  have atZero : Nonempty (Derivation B (H :: Γ) (memberGraph z key)) := by
    change Nonempty (Derivation B (H :: Γ) (programGraph scratchMember (suc z) ![z,key]))
    have m := Derivation.conjunctionRight h
    change Derivation B (H :: Γ) (programGraph scratchMember (suc z) ![out,key]) at m
    unfold programGraph at m ⊢
    apply graphInputTransport B α 2 (H :: Γ) (OrdinaryArithmetic.graphFormula scratchMember)
      (suc z) ![out,key] ![z,key] _ ⟨m⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Nonempty (Derivation B (H :: Γ) (equal out z))
      rw [equalEqn]
      exact ⟨cancelSuc eq⟩
    · obtain rfl := Fin.eq_zero j
      change Nonempty (Derivation B (H :: Γ) (equal key key))
      rw [equalEqn]
      exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl key⟩
  obtain ⟨bad⟩ := nilMemberFalse key atZero
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion bad)⟩

private theorem stepOrigin (code row tail out h p key : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code row tail)))
    (ih : Nonempty (Derivation B Γ (allOutputs tail key)))
    (guard : Nonempty (Derivation B Γ (unary (guardAt 4) (suc z) row)))
    (field0 : Nonempty (Derivation B Γ (unary (field 0) h row)))
    (recursive : Nonempty (Derivation B Γ (unary scratchTargets (suc p) tail)))
    (cellOut : Nonempty (Derivation B Γ (consGraph out h p)))
    (member : Nonempty (Derivation B Γ (memberGraph out key))) :
    Nonempty (Derivation B Γ (origin code key)) := by
  obtain ⟨choice⟩ := consInversion out h p key cellOut member
  obtain ⟨g⟩ := guard
  obtain ⟨f⟩ := field0
  obtain ⟨r⟩ := recursive
  obtain ⟨c⟩ := cell
  obtain ⟨i⟩ := ih
  let L := (missGraph h key).not
  let R := memberGraph p key
  have l : Nonempty (Derivation B Γ (L.imp (origin code key))) := by
    have own : Derivation B (L :: Γ) L := Derivation.hypothesis List.mem_cons_self
    have e := equalityOfHit h key (body := B) (Γ := L :: Γ) ⟨own⟩
    obtain ⟨val⟩ := outputTransport (field 0) h key ![row] e ⟨addHyp f L⟩
    obtain ⟨m⟩ := headMember code row tail row ⟨addHyp c L⟩
      ⟨ID1Completion.InternalTagArithmeticSupportProof.refl row⟩
    obtain ⟨ours⟩ := witness code key row (Derivation.conjunctionIntroduction m
      (Derivation.conjunctionIntroduction (addHyp g L) val))
    exact ⟨Derivation.implicationIntroduction ours⟩
  have rt : Nonempty (Derivation B Γ (R.imp (origin code key))) := by
    obtain ⟨j⟩ := useAtOutput tail key p ⟨addHyp i R⟩
    have own : Derivation B (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
    have raw := Derivation.implicationElimination j (Derivation.conjunctionIntroduction (addHyp r R) own)
    obtain ⟨ours⟩ := liftOrigin code row tail key ⟨addHyp c R⟩ ⟨raw⟩
    exact ⟨Derivation.implicationIntroduction ours⟩
  obtain ⟨hl⟩ := l
  obtain ⟨hr⟩ := rt
  exact ⟨disjunctionElimination choice hl hr⟩

theorem consAt (code row tail key out : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code row tail)))
    (ih : Nonempty (Derivation B Γ (allOutputs tail key))) :
    Nonempty (Derivation B Γ (atOutput code key out)) := by
  let H := unary scratchTargets (suc out) code ⊓ memberGraph out key
  have own : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨c⟩ := cell
  obtain ⟨i⟩ := ih
  have actual : Nonempty (Derivation B (H :: Γ) (origin code key)) := by
    apply exactOpenTargetMapCons B α (H :: Γ) code row tail out (origin code key)
      ⟨addHyp c H⟩ ⟨Derivation.conjunctionLeft own⟩
    intro β j Δ h p keep guard field0 tailRun projected
    have c' := renameInto (show Nonempty (Derivation B (H :: Γ) (consGraph code row tail))
      from ⟨addHyp c H⟩) j Δ keep
    rw [consGraphRename] at c'
    have ih' := renameInto (show Nonempty (Derivation B (H :: Γ) (allOutputs tail key))
      from ⟨addHyp i H⟩) j Δ keep
    rw [allOutputsRename] at ih'
    have m := renameInto (show Nonempty (Derivation B (H :: Γ) (memberGraph out key))
      from ⟨Derivation.conjunctionRight own⟩) j Δ keep
    rw [graphRename] at m
    rw [originRename]
    exact stepOrigin (code.relabel j) (row.relabel j) (tail.relabel j) (out.relabel j) h p
      (key.relabel j) c' ih' guard field0 tailRun projected m
  obtain ⟨result⟩ := actual
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginStepProof
