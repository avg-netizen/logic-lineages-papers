module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ListGeometryTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalListCodecSupportProof (consGraph)
open InternalListInduction InternalListInductionSyntaxProof InternalListInductionProof
open ReverseAppendSyntaxProof ReverseAppendCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map
  InternalApplicationValidityStackAppend.append InternalListCodec.consCode

theorem zeroRow : Nonempty (Derivation body Delta (row (z : OTerm alpha))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 6 Delta
  let right : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let mappedLeft : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let mappedRight : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let out : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := fields z right joined parameter mappedLeft mappedRight out
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
  obtain ⟨h⟩ := zeroCore right joined parameter mappedLeft mappedRight out
    (body := body) (Delta := Theta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem consRow (code head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hi : Nonempty (Derivation body Delta (row tail))) :
    Nonempty (Derivation body Delta (row code)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 6 Delta
  let right : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let mappedLeft : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let mappedRight : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let out : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := fields (code.relabel Sum.inl) right joined parameter mappedLeft mappedRight out
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
  have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 6) ∈ Theta := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have hc := renameInto hc Sum.inl Theta inc
  have hi := renameInto hi Sum.inl Theta inc
  rw [graph2Rename] at hc
  rw [rowRename] at hi
  obtain ⟨h⟩ := consCore (code.relabel Sum.inl) (head.relabel Sum.inl) (tail.relabel Sum.inl)
    right joined parameter mappedLeft mappedRight out hc hi
    (show Nonempty (Derivation body Theta A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- The existing original arithmetic list-code induction discharges the full
actual map/append invariant at every internally quantified numeric code. -/
theorem allRows (left : OTerm alpha) :
    Nonempty (Derivation body Delta (row left)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (atCode theta z)) := by
    rw [rowAtCode]
    exact zeroRow
  have hs : Nonempty (Derivation body Delta (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body alpha 3 Delta
    simp only [constructorBody,theta,rowAtIndex]
    let code : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
    let head : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
    let tail : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
    let C := consGraph code head tail
    let IH := row tail
    obtain ⟨d⟩ := consRow code head tail
      (body := body) (Delta := IH :: C :: Delta.map (fun f => f.relabel Sum.inl))
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  have h := actualOriginalListInductionAtCode body alpha Delta theta left (andIntro hz hs)
  rw [rowAtCode] at h
  exact h

theorem actualReverseAppend : ListGeometryTargets.ReverseAppend := by
  intro body alpha Delta left right joined mappedLeft mappedRight out hj hl hr ho
  exact rowApply left right joined z mappedLeft mappedRight out
    (allRows left) (andIntro hj (andIntro hl (andIntro hr ho)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendProof.actualReverseAppend
