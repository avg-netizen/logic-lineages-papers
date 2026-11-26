module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthProof
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
open OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsScanLengthSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem scanZero (Q : Program 2) (input parameter : OTerm alpha) :
    Nonempty (Derivation body Delta (graph3 (scan Q) z z input parameter)) :=
  recursionZeroValue (InternalAcceptance.constantZero 2) (step Q) z
    (Fin.cons input (Fin.cons parameter Fin.elim0)) (InternalRawListRecursionSupportProof.constantZero _)

theorem zeroCore (Q : Program 2) (input parameter out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 (scan Q) out z input parameter))) :
    Nonempty (Derivation body Delta (lengthGraph z out)) := by
  obtain ⟨he⟩ := valueUnique (scan Q) z out
    (Fin.cons z (Fin.cons input (Fin.cons parameter Fin.elim0))) (scanZero Q input parameter) hs
  exact headTransport length z z out Fin.elim0 ⟨he⟩ lengthZero

theorem succCore (Q : Program 2) (count input parameter out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row Q count)))
    (hs : Nonempty (Derivation body Delta (graph3 (scan Q) out (suc count) input parameter))) :
    Nonempty (Derivation body Delta (lengthGraph (suc count) out)) := by
  apply OriginalHereditaryDeletionRowsCasesProof.scanCases Q count input parameter _
  intro beta j Theta previous value singleton hj hp hv hc
  simp only [lengthRename,sucRelabel]
  have hr' := renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hs' := renameInto hs j Theta hj
  simp only [graph3Rename,sucRelabel] at hs'
  have hl := rowApply Q (count.relabel j) (input.relabel j) (parameter.relabel j) previous hr' hp
  have ha := OriginalHereditaryDeletionRowsStepProof.scanAppendRecover Q
    (count.relabel j) previous (input.relabel j) (parameter.relabel j) value singleton (out.relabel j)
    hp hs' hv hc
  exact OriginalHereditaryDeletionRowsLengthProof.appendSingletonLength
    (count.relabel j) previous value singleton (out.relabel j) hl hc ha

theorem zeroRow (Q : Program 2) : Nonempty (Derivation body Delta (row Q z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let input : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let parameter : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := graph3 (scan Q) out z input parameter
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    Q input parameter out ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (Q : Program 2) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row Q count))) :
    Nonempty (Derivation body Delta (row Q (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let input : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let parameter : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let A := graph3 (scan Q) out (suc c) input parameter
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore Q c input parameter out hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (Q : Program 2) (count : OTerm alpha) : Nonempty (Derivation body Delta (row Q count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row Q (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) Q)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      Q (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem scanLength (Q : Program 2) (count input parameter out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 (scan Q) out count input parameter))) :
    Nonempty (Derivation body Delta (lengthGraph count out)) :=
  rowApply Q count input parameter out (allRows Q count) hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthProof
