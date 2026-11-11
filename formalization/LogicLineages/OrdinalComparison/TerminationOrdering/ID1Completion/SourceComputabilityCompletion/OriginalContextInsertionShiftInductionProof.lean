module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalListCodecSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalListInduction InternalListInductionProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionShiftSyntaxProof OriginalContextInsertionShiftCoreProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem zeroRow : Nonempty (Derivation body Gamma (shiftRow (z : OTerm alpha))) := by
  unfold shiftRow
  apply actualFiniteUniversalIntroduction body alpha 6 Gamma
  let out : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let typ : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let count : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let suffix : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let index : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := lengthGraph count z ⊓
    graph2 InternalApplicationValidityStackAppend.append joined z suffix
  have h : Nonempty (Derivation body (A :: Gamma.map (fun p => p.relabel Sum.inl)) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := zeroCore out typ count suffix joined index (andLeft h) (andRight h)
  simpa only [shiftBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

 theorem consRow (front head tail : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (shiftRow tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph front head tail))) :
    Nonempty (Derivation body Gamma (shiftRow front)) := by
  unfold shiftRow
  apply actualFiniteUniversalIntroduction body alpha 6 Gamma
  let out : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let typ : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let count : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let suffix : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let index : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let f := front.relabel (Sum.inl : alpha → alpha ⊕ Fin 6)
  let h := head.relabel (Sum.inl : alpha → alpha ⊕ Fin 6)
  let t := tail.relabel (Sum.inl : alpha → alpha ⊕ Fin 6)
  let A := lengthGraph count f ⊓
    graph2 InternalApplicationValidityStackAppend.append joined f suffix
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [shiftRename] at hrow'
  have hc' := renameInto hc Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [consGraphRename] at hc'
  have hp : Nonempty (Derivation body Delta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := consCore f h t out typ count suffix joined index hrow' hc'
    (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction d⟩

/-- The original arithmetic list-code induction is applied to every raw
front code. Native decoding and evaluation are absent from this proof. -/
 theorem allRows (front : OTerm alpha) :
    Nonempty (Derivation body Gamma (shiftRow front)) := by
  let theta : Formula (alpha ⊕ Fin 1) := shiftRow (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (atCode theta z)) := by
    rw [shiftAtCode]
    exact zeroRow
  have hs : Nonempty (Derivation body Gamma (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body alpha 3 Gamma
    simp only [constructorBody,theta,shiftAtIndex]
    let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
    let h : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
    let t : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
    let C := consGraph c h t
    let R := shiftRow t
    obtain ⟨d⟩ := consRow (body := body)
      (Gamma := R :: C :: Gamma.map (fun p => p.relabel Sum.inl)) c h t
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  have h := actualOriginalListInductionAtCode body alpha Gamma theta front (andIntro hz hs)
  rw [shiftAtCode] at h
  exact h

 theorem appendShift (front out typ count suffix joined index : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ (add count index) joined).iff
        (OriginalVariableDecoder.graph out typ index suffix))) :=
  rowApply front out typ count suffix joined index (allRows front) hl ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftInductionProof
