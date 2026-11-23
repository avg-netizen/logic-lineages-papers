module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryWholeBottomProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreeMembershipCoreProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalAccessibilityIntroduction)
open ID1Completion.InternalComputabilityDownwardProof (edgeCases)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalAtomicMembershipSyntaxProof (underSuccessor membershipRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalAtomicRefinement (atSource bottomTarget)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (callSlot)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm sourceFields)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm freeTerm)
open NumberedWindowInternalAuxBottomRefinementObjectTargets (packedAuxBottomTerm)
open NumberedWindowInternalAuxBottomRefinement (sourceFlag)
open NumberedWindowInternalNeutralAuxiliaryRefinement (freeAux auxDom auxFnType)
open NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionProof (exact_OriginalNeutralAuxiliaryRecognition)
open NumberedWindowInternalNeutralAuxiliaryRefinementObjectBranchProof
  (exact_OpenFreeAuxBranch exact_OpenFreeAuxTargetCases)
open NumberedWindowInternalNeutralAuxiliaryBottomTargetProof (exact_OriginalNeutralBottomAuxTarget)
open NumberedWindowInternalNeutralAuxiliaryWholeBottomProof (exact_OpenNeutralWholeBottom)
open NumberedWindowInternalNeutralAuxiliaryLiteralBodyProof
  (literalNeutral exact_OpenLiteralNeutralCertificate exact_OpenLiteralNeutralBottomI
    exact_OpenLiteralNeutralBottomAuxI)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)

attribute [local irreducible] programGraph

/-- The remaining arithmetic field-opening interface. It only recovers
the actual packed shape and an unspecified right argument, not I. -/
def BottomTargetShapeCases : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (y ctx dom cod stored : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (unary sourceFlag (suc z) y ⊓
      (sourceFields y ctx cod ⊓ (unary auxDom dom y ⊓ unary auxFnType stored y)))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (arg : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (equal (y.relabel j)
        (packedAuxBottomTerm (ctx.relabel j) (dom.relabel j)
          (cod.relabel j) (stored.relabel j) arg))) →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

private def sourceTail {α : Type} (x ctx dom cod stored : OTerm α) : Formula α :=
  sourceFields x ctx cod ⊓ (unary auxDom dom x ⊓ unary auxFnType stored x)

private theorem sourceFieldsRename {α β : Type} (x ctx cod : OTerm α) (j : α → β) :
    (sourceFields x ctx cod).relabel j =
      sourceFields (x.relabel j) (ctx.relabel j) (cod.relabel j) := by
  change (unary rawContext ctx x ⊓ unary rawResult cod x).relabel j =
    (unary rawContext (ctx.relabel j) (x.relabel j) ⊓ unary rawResult (cod.relabel j) (x.relabel j))
  simp only [conjunctionRename,unaryRename]

private theorem tailRename {α β : Type} (x ctx dom cod stored : OTerm α) (j : α → β) :
    (sourceTail x ctx dom cod stored).relabel j =
      sourceTail (x.relabel j) (ctx.relabel j) (dom.relabel j) (cod.relabel j) (stored.relabel j) := by
  simp only [sourceTail,conjunctionRename,sourceFieldsRename,unaryRename]

/-- Original ID1 computes I for a carried free-headed auxiliary once the
pure arithmetic bottom-target parser is supplied. Uses the exact same
body for all source and successor accessibility statements. -/
theorem exact_OpenLiteralNeutralFreeAuxICore (unpack : BottomTargetShapeCases)
    (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x ctx dom cod stored name arg : OTerm α)
    (shape : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (equal x (auxAddressTerm ctx dom cod (freeTerm stored name) arg))))
    (held : Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ
      (carrier (literalNeutral i r) false c x))) :
    Nonempty (Derivation (sourceBody (literalNeutral i r) c) Γ (membership false x)) := by
  let S := literalNeutral i r
  let B := sourceBody S c
  obtain ⟨data⟩ := exact_OriginalNeutralAuxiliaryRecognition B α Γ x ctx dom cod stored name arg shape
  have flag : Nonempty (Derivation B Γ (unary freeAux (suc z) x)) :=
    ⟨Derivation.conjunctionLeft data⟩
  have fields : Nonempty (Derivation B Γ (sourceTail x ctx dom cod stored)) :=
    ⟨Derivation.conjunctionRight data⟩
  apply actualOriginalAccessibilityIntroduction S false c α Γ x held
  let j : α → α ⊕ Fin 1 := Sum.inl
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H := edge S false c (x.relabel j) y
  let A := H :: Γ.map weaken
  have members := underSuccessor Γ H
  have hEdge : Nonempty (Derivation B A H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have fA := renameInto flag j A members
  simp only [unaryRename,sucRelabel,zRelabel] at fA
  have tA := renameInto fields j A members
  rw [tailRename] at tA
  have succI : Nonempty (Derivation B A (membership false y)) := by
    apply edgeCases S c (x.relabel j) y _ hEdge
    intro β k Δ w keep cert
    rw [membershipRename]
    let x' := (x.relabel j).relabel k
    let y' := y.relabel k
    let ctx' := (ctx.relabel j).relabel k
    let dom' := (dom.relabel j).relabel k
    let cod' := (cod.relabel j).relabel k
    let stored' := (stored.relabel j).relabel k
    obtain ⟨edgeReport⟩ := exact_OpenLiteralNeutralCertificate i r c β Δ x' w y' cert
    have gain : Nonempty (Derivation B Δ (carrier S false c y')) :=
      ⟨Derivation.conjunctionRight edgeReport⟩
    have fD := renameInto fA k Δ keep
    simp only [unaryRename,sucRelabel,zRelabel] at fD
    have tD := renameInto tA k Δ keep
    rw [tailRename] at tD
    have inSlot : Nonempty (Derivation B Δ
      (programGraph (atSource freeAux) (suc z) ![x',w,y'])) := callSlot freeAux 0 (suc z) ![x',w,y'] fD
    obtain ⟨opened⟩ := exact_OpenFreeAuxBranch i r x' w y' inSlot
      ⟨Derivation.conjunctionLeft edgeReport⟩
    apply exact_OpenFreeAuxTargetCases i x' w y' (membership false y')
      ⟨Derivation.conjunctionRight opened⟩
    · intro γ h Θ stays checked
      rw [membershipRename]
      have atSource := renameInto tD h Θ stays
      rw [tailRename] at atSource
      have carries := renameInto gain h Θ stays
      rw [carrierRename] at carries
      have t := exact_OriginalNeutralBottomAuxTarget (x'.relabel h) (w.relabel h) (y'.relabel h)
        (ctx'.relabel h) (cod'.relabel h) (dom'.relabel h) (stored'.relabel h) atSource checked
      apply unpack B γ Θ (y'.relabel h) (ctx'.relabel h) (dom'.relabel h)
        (cod'.relabel h) (stored'.relabel h) (membership false (y'.relabel h)) t
      intro ε u Ω rawArg kept packed
      rw [membershipRename]
      have also := renameInto carries u Ω kept
      rw [carrierRename] at also
      exact exact_OpenLiteralNeutralBottomAuxI i r c ε Ω _ _ _ _ _ rawArg packed also
    · intro γ h Θ stays checked
      rw [membershipRename]
      have atSource := renameInto tD h Θ stays
      rw [tailRename] at atSource
      obtain ⟨left⟩ := atSource
      obtain ⟨right⟩ := checked
      have final := exact_OpenNeutralWholeBottom (x'.relabel h) (w.relabel h)
        (y'.relabel h) (ctx'.relabel h) (cod'.relabel h)
        ⟨Derivation.conjunctionLeft left⟩ ⟨Derivation.conjunctionLeft right⟩
      have carries := renameInto gain h Θ stays
      rw [carrierRename] at carries
      exact exact_OpenLiteralNeutralBottomI i r c γ Θ _ _ _ final carries
  obtain ⟨success⟩ := succI
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction success)⟩

#print axioms exact_OpenLiteralNeutralFreeAuxICore
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryFreeMembershipCoreProof
