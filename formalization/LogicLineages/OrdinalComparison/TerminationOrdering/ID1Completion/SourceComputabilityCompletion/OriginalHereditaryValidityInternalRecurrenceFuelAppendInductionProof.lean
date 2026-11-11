module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalListInduction InternalListInductionProof
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelAppendSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelAppendCoreProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem zeroRow : Nonempty (Derivation body Delta (fuelAppendRow (z : OTerm alpha))) := by
  unfold fuelAppendRow
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let suffix : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let joined : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let first : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let second : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := graph2 InternalApplicationValidityStackAppend.append joined z suffix ⊓
    (WorkFuelGraph first z ⊓ WorkFuelGraph second suffix)
  have h : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := zeroCore suffix joined first second
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  simpa only [fuelAppendBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

 theorem consRow (front frame rest : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (fuelAppendRow rest)))
    (hc : Nonempty (Derivation body Delta (WorkCons front frame rest))) :
    Nonempty (Derivation body Delta (fuelAppendRow front)) := by
  unfold fuelAppendRow
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let suffix : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let joined : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let first : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let second : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let f := front.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let h := frame.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let t := rest.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let A := graph2 InternalApplicationValidityStackAppend.append joined f suffix ⊓
    (WorkFuelGraph first f ⊓ WorkFuelGraph second suffix)
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [fuelAppendRename] at hrow'
  have hc' := renameInto hc Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  simp only [WorkCons,graph2Rename] at hc'
  have hp : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := consCore f h t suffix joined first second hrow' hc'
    (andLeft hp) (andLeft (andRight hp)) (andRight (andRight hp))
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Object-language list-code induction over every original raw front code. -/
 theorem allRows (front : OTerm alpha) :
    Nonempty (Derivation body Delta (fuelAppendRow front)) := by
  let theta : Formula (alpha ⊕ Fin 1) := fuelAppendRow (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (atCode theta z)) := by
    rw [fuelAppendAtCode]
    exact zeroRow
  have hs : Nonempty (Derivation body Delta (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body alpha 3 Delta
    simp only [constructorBody,theta,fuelAppendAtIndex]
    let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
    let h : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
    let t : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
    let C := WorkCons c h t
    let R := fuelAppendRow t
    obtain ⟨d⟩ := consRow (body := body)
      (Delta := R :: C :: Delta.map (fun p => p.relabel Sum.inl)) c h t
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  have h := actualOriginalListInductionAtCode body alpha Delta theta front (andIntro hz hs)
  rw [fuelAppendAtCode] at h
  exact h

 theorem appendValue (front suffix joined first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph first front)))
    (hs : Nonempty (Derivation body Delta (WorkFuelGraph second suffix))) :
    Nonempty (Derivation body Delta (WorkFuelGraph (add first second) joined)) :=
  rowApply front suffix joined first second (allRows front) ha hf hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof
