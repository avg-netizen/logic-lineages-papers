module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus JointGammaInvariant InternalSliceInduction SourceComputabilityFormulaSupportProof
open SourceEndpoint TaggedArithmeticOperators InternalSliceInductionSyntaxProof
open InternalSliceInductionSupportProof InternalInvariantSelectionProof

theorem actualInternalPairedClosure : InternalSliceInductionTargets.ActualInternalPairedClosure := by
  intro data context α Gamma scalar multiset hs hm
  obtain ⟨hs⟩ := hs
  obtain ⟨hm⟩ := hm
  let body := SourcePresentation.sourceBody data context
  let scalarBody := specialize (SourcePresentation.scalarOperator data) context
  let multisetBody := specialize (SourcePresentation.multisetOperator data) context
  let scalarReplacement := replacedBody
    (specialize (tagPredicate false (SourcePresentation.scalarOperator data)) context)
    (tagged scalar multiset)
  let multisetReplacement := replacedBody
    (specialize (tagPredicate true (SourcePresentation.multisetOperator data)) context)
    (tagged scalar multiset)
  change Derivation body (replacedBody scalarBody scalar :: Gamma.map weaken) scalar at hs
  change Derivation body (replacedBody multisetBody multiset :: Gamma.map weaken) multiset at hm
  obtain ⟨selectS⟩ := selectedReplacement body (SourcePresentation.scalarOperator data)
    context false scalar multiset
  obtain ⟨selectM⟩ := selectedReplacement body (SourcePresentation.multisetOperator data)
    context true scalar multiset
  obtain ⟨branchS⟩ := branchTransport Gamma false scalarReplacement scalar
    ⟨precompose (Derivation.implicationIntroduction hs) selectS⟩
  obtain ⟨branchM⟩ := branchTransport Gamma true multisetReplacement multiset
    ⟨precompose (Derivation.implicationIntroduction hm) selectM⟩
  apply Nonempty.intro
  let Delta := replacedBody body (tagged scalar multiset) :: Gamma.map weaken
  have h : Derivation body Delta (replacedBody body (tagged scalar multiset)) :=
    Derivation.hypothesis List.mem_cons_self
  change Derivation body Delta
    ((replacedBody (specialize (taggedBranch false (SourcePresentation.scalarOperator data)) context)
      (tagged scalar multiset)) ⊓
     (replacedBody (specialize (taggedBranch true (SourcePresentation.multisetOperator data)) context)
      (tagged scalar multiset))) at h
  rw [replacementBranch,replacementBranch] at h
  exact Derivation.conjunctionIntroduction
    (Derivation.implicationElimination
      (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp) branchS)
      (Derivation.conjunctionLeft h))
    (Derivation.implicationElimination
      (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp) branchM)
      (Derivation.conjunctionRight h))

theorem actualInternalSliceInduction : InternalSliceInductionTargets.ActualInternalSliceInduction := by
  intro data context α Gamma odd theta t hstep
  cases odd with
  | false =>
    have hclosure := actualInternalPairedClosure data context α Gamma theta (currentSlice true)
      hstep (currentClosure data context α Gamma true)
    exact (actualSelectedInvariantInduction data context α Gamma theta (currentSlice true)
      t hclosure).1
  | true =>
    have hclosure := actualInternalPairedClosure data context α Gamma (currentSlice false) theta
      (currentClosure data context α Gamma false) hstep
    exact (actualSelectedInvariantInduction data context α Gamma (currentSlice false) theta
      t hclosure).2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionProof
