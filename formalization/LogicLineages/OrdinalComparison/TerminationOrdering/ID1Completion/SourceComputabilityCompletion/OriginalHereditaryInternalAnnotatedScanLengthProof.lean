module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalHereditaryAnnotatedExpansion OriginalHereditaryInternalAnnotatedScanLengthSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem scanZero (role typ raw jobs : OTerm alpha) :
    Nonempty (Derivation body Delta (graph5 scan z z role typ raw jobs)) :=
  recursionZeroValue (InternalAcceptance.constantZero 4) scanStep z
    (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))) (InternalRawListRecursionSupportProof.constantZero _)

theorem zeroCore (role typ raw jobs out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph5 scan out z role typ raw jobs))) :
    Nonempty (Derivation body Delta (lengthGraph z out)) := by
  obtain ⟨he⟩ := valueUnique scan z out
    (Fin.cons z (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))) (scanZero role typ raw jobs) hs
  exact headTransport length z z out Fin.elim0 ⟨he⟩ lengthZero

theorem succCore (count role typ raw jobs out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row count)))
    (hs : Nonempty (Derivation body Delta (graph5 scan out (suc count) role typ raw jobs))) :
    Nonempty (Derivation body Delta (lengthGraph (suc count) out)) := by
  apply OriginalHereditaryInternalAnnotatedScanLengthCasesProof.scanCases count role typ raw jobs _
  intro beta j Theta previous value singleton hj hp hv hc
  simp only [lengthRename,sucRelabel]
  have hr' := renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hs' := renameInto hs j Theta hj
  simp only [graph5Rename,sucRelabel] at hs'
  have hl := rowApply (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j) previous hr' hp
  have ha := OriginalHereditaryInternalAnnotatedScanLengthStepProof.scanAppendRecover
    (count.relabel j) previous (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j) value singleton (out.relabel j)
    hp hs' hv hc
  exact OriginalHereditaryDeletionRowsLengthProof.appendSingletonLength
    (count.relabel j) previous value singleton (out.relabel j) hl hc ha

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 5 Delta
  let role : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let typ : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let raw : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let jobs : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := graph5 scan out z role typ raw jobs
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    role typ raw jobs out ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count))) :
    Nonempty (Derivation body Delta (row (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 5 Delta
  let role : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let typ : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let raw : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let jobs : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
  let A := graph5 scan out (suc c) role typ raw jobs
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore c role typ raw jobs out hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
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

theorem scanLength (count role typ raw jobs out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph5 scan out count role typ raw jobs))) :
    Nonempty (Derivation body Delta (lengthGraph count out)) :=
  rowApply count role typ raw jobs out (allRows count) hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthProof
