module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthProof
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
open Continuation20261115.OriginalCodeDecoderTable Continuation20261115.OriginalCodeDecoderTable.LengthSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (n : Nat) (previous out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (nextRow n) out z previous))) :
    Nonempty (Derivation body Delta (lengthGraph (suc z) out)) := by
  apply InternalAcceptanceSupportProof.programCases (OriginalCodeDecoderStep.step n)
    (Fin.cons previous (Fin.cons z Fin.elim0)) _
  intro beta j Theta value hj hv
  simp only [lengthRename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hv
  have hs' := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,zRelabel] at hs'
  have hc := SupportProof.baseRecover n (previous.relabel j) value (out.relabel j) hv hs'
  exact lengthCons (out.relabel j) value z z hc lengthZero

theorem succCore (n : Nat) (count previous out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row n count)))
    (hs : Nonempty (Derivation body Delta (graph2 (nextRow n) out (suc count) previous))) :
    Nonempty (Derivation body Delta (lengthGraph (suc (suc count)) out)) := by
  apply SupportProof.rowCases n count previous _
  intro beta j Theta front value singleton hj hp hv hc
  simp only [lengthRename,sucRelabel]
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hs' := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,sucRelabel] at hs'
  have hl := rowApply n (count.relabel j) (previous.relabel j) front hr' hp
  have ha := SupportProof.appendRecover n (count.relabel j) front (previous.relabel j)
    value singleton (out.relabel j) hp hs' hv hc
  exact OriginalHereditaryDeletionRowsLengthProof.appendSingletonLength
    (suc (count.relabel j)) front value singleton (out.relabel j) hl hc ha

theorem zeroRow (n : Nat) : Nonempty (Derivation body Delta (row n z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 2 Delta
  let previous : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let A := graph2 (nextRow n) out z previous
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    n previous out ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (n : Nat) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row n count))) :
    Nonempty (Derivation body Delta (row n (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 2 Delta
  let previous : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 2)
  let A := graph2 (nextRow n) out (suc c) previous
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
  have hrow' := InternalGraphCompositionFunctionalityProof.renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore n c previous out hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (n : Nat) (count : OTerm alpha) : Nonempty (Derivation body Delta (row n count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row n (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) n)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      n (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem rowLength (n : Nat) (count previous out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (nextRow n) out count previous))) :
    Nonempty (Derivation body Delta (lengthGraph (suc count) out)) :=
  rowApply n count previous out (allRows n count) hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthProof
