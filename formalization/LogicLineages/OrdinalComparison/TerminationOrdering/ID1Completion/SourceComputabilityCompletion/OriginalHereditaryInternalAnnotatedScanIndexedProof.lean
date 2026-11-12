module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedCoreProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalHereditaryDeletionRows OriginalHereditaryInternalAnnotatedScanIndexedSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open OriginalHereditaryInternalAnnotatedScanIndexedCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 7 Delta
  let role : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let typ : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let raw : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let jobs : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let output : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let cutoff : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let value : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let A := fields z role typ raw jobs output cutoff value
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    role typ raw jobs output cutoff value ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count))) :
    Nonempty (Derivation body Delta (row (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 7 Delta
  let role : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let typ : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let raw : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let jobs : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let output : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let cutoff : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let value : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 7)
  let A := fields (suc c) role typ raw jobs output cutoff value
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 7))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore c role typ raw jobs output cutoff value hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (count : OTerm alpha) : Nonempty (Derivation body Delta (row count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem actualIndexed : OriginalHereditaryInternalAnnotatedScanTargets.Indexed := by
 intro body alpha Delta count role typ raw jobs output cutoff value hs hb hv
 exact rowApply count role typ raw jobs output cutoff value (allRows count)
   (InternalApplicationStepPeelSupportProof.andIntro hb
     (InternalApplicationStepPeelSupportProof.andIntro hs hv))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedProof
