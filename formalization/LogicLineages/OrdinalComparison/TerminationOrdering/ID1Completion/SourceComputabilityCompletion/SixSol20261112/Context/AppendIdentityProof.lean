module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalListCodecSupportProof (consGraph consGraphRename)
open InternalListInduction InternalListInductionSyntaxProof InternalListInductionProof
open AppendIdentitySyntaxProof AppendIdentityCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalApplicationValidityStackAppend.append
  InternalListCodec.consCode

theorem zeroCancels : Nonempty (Derivation body Delta (cancels (z : OTerm alpha))) := by
  unfold cancels
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let left : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let right : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let joined : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields z left right joined
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  obtain ⟨h⟩ := zeroCancel left right joined (body := body) (Delta := Theta)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [cancelBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem zeroRow : Nonempty (Derivation body Delta (row (z : OTerm alpha))) :=
  andIntro (InternalApplicationValidityStackAppendListProof.appendZeroValue z) zeroCancels

theorem consCancels (front head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
    (hi : Nonempty (Derivation body Delta (cancels tail))) :
    Nonempty (Derivation body Delta (cancels front)) := by
  unfold cancels
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let left : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let right : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let joined : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields (front.relabel Sum.inl) left right joined
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have hc' := renameInto hc Sum.inl Theta inc
  rw [consGraphRename] at hc'
  have hi' := renameInto hi Sum.inl Theta inc
  rw [cancelsRename] at hi'
  obtain ⟨h⟩ := consCancel (front.relabel Sum.inl) (head.relabel Sum.inl) (tail.relabel Sum.inl)
    left right joined hc' hi'
    (show Nonempty (Derivation body Theta A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem consRow (front head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
    (hi : Nonempty (Derivation body Delta (row tail))) :
    Nonempty (Derivation body Delta (row front)) := by
  have hz := InternalApplicationValidityStackAppendListProof.consBackward
    front head tail z tail front hc (andLeft hi) hc
  exact andIntro hz (consCancels front head tail hc (andRight hi))

theorem allRows (front : OTerm alpha) : Nonempty (Derivation body Delta (row front)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (atCode theta z)) := by
    rw [AppendIdentitySyntaxProof.rowAtCode]
    exact zeroRow
  have hs : Nonempty (Derivation body Delta (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body alpha 3 Delta
    simp only [constructorBody,theta,AppendIdentitySyntaxProof.rowAtIndex]
    let code : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
    let head : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
    let tail : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
    let C := consGraph code head tail
    let IH := row tail
    obtain ⟨h⟩ := consRow code head tail
      (body := body) (Delta := IH :: C :: Delta.map (fun f => f.relabel Sum.inl))
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩
  have h := actualOriginalListInductionAtCode body alpha Delta theta front (andIntro hz hs)
  rw [AppendIdentitySyntaxProof.rowAtCode] at h
  exact h

theorem actualRightZero : AppendIdentityTargets.ActualRightZero := by
  intro body alpha Delta front
  exact andLeft (allRows (body := body) (Delta := Delta) front)

theorem actualLeftCancellation : AppendIdentityTargets.ActualLeftCancellation := by
  intro body alpha Delta front left right joined hl hr
  exact cancelApply front left right joined (andRight (allRows front)) (andIntro hl hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof.actualRightZero
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof.actualLeftCancellation
