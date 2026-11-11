module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalListInduction InternalListInductionProof InternalOriginalOrderSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionVariableSupportProof
open OriginalContextInsertionBelowSyntaxProof OriginalContextInsertionBelowCoreProof
open OriginalContextInsertionBelowConsProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem zeroRow : Nonempty (Derivation body Gamma (belowRow (z : OTerm alpha))) := by
  unfold belowRow
  apply actualFiniteUniversalIntroduction body alpha 6 Gamma
  let out : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let typ : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let count : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let suffix : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let index : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := lengthGraph count z ⊓
    (graph2 InternalApplicationValidityStackAppend.append joined z suffix ⊓ ltF index count)
  have h : Nonempty (Derivation body (A :: Gamma.map (fun p => p.relabel Sum.inl)) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := zeroCore out typ count joined index (andLeft h) (andRight (andRight h))
  simpa only [belowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

 theorem consRow (front head tail : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (belowRow tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph front head tail))) :
    Nonempty (Derivation body Gamma (belowRow front)) := by
  unfold belowRow
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
    (graph2 InternalApplicationValidityStackAppend.append joined f suffix ⊓ ltF index count)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [belowRename] at hrow'
  have hc' := renameInto hc Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [consGraphRename] at hc'
  have hp : Nonempty (Derivation body Delta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := consCore f h t out typ count suffix joined index hrow' hc'
    (andLeft hp) (andLeft (andRight hp)) (andRight (andRight hp))
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Original arithmetic list-code induction establishes suffix independence
for every raw front. No native evaluation or decoded context is a premise. -/
 theorem allRows (front : OTerm alpha) :
    Nonempty (Derivation body Gamma (belowRow front)) := by
  let theta : Formula (alpha ⊕ Fin 1) := belowRow (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (atCode theta z)) := by
    rw [belowAtCode]
    exact zeroRow
  have hs : Nonempty (Derivation body Gamma (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body alpha 3 Gamma
    simp only [constructorBody,theta,belowAtIndex]
    let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
    let h : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
    let t : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
    let C := consGraph c h t
    let R := belowRow t
    obtain ⟨d⟩ := consRow (body := body)
      (Gamma := R :: C :: Gamma.map (fun p => p.relabel Sum.inl)) c h t
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  have h := actualOriginalListInductionAtCode body alpha Gamma theta front (andIntro hz hs)
  rw [belowAtCode] at h
  exact h

 theorem appendBelow (front out typ count suffix joined index : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hb : Nonempty (Derivation body Gamma (ltF index count))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index joined).iff
        (OriginalVariableDecoder.graph out typ index front))) :=
  rowApply front out typ count suffix joined index (allRows front) hl ha hb

/-- Both outputs are compared with the SAME original front code. -/
 theorem samePrefixBelow
    (front out typ count suffix joined otherSuffix otherJoined index : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hc : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append otherJoined front otherSuffix)))
    (hb : Nonempty (Derivation body Gamma (ltF index count))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index joined).iff
        (OriginalVariableDecoder.graph out typ index otherJoined))) :=
  iffTrans (appendBelow front out typ count suffix joined index hl ha hb)
    (iffSymm (appendBelow front out typ count otherSuffix otherJoined index hl hc hb))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowInductionProof
