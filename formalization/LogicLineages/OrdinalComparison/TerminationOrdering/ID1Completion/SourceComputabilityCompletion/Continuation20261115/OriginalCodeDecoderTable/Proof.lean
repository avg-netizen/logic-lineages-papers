module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Proof
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
open Continuation20261115.OriginalCodeDecoderTable Continuation20261115.OriginalCodeDecoderTable.IndexSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open Continuation20261115.OriginalCodeDecoderTable.IndexCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow (n : Nat) : Nonempty (Derivation body Delta (row n z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let oldTable : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let output : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let cutoff : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let value : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := fields n z oldTable output cutoff value
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    n oldTable output cutoff value ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (n : Nat) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row n count))) :
    Nonempty (Derivation body Delta (row n (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let oldTable : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let output : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let cutoff : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let value : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let A := fields n (suc c) oldTable output cutoff value
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hrow' := InternalGraphCompositionFunctionalityProof.renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore n c oldTable output cutoff value hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
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

theorem internalRowLookup : Targets.InternalRowLookup := by
  intro n body alpha Delta count previous output cutoff value hp hb hv
  exact rowApply n count previous output cutoff value (allRows n count)
    (andIntro hb (andIntro hp hv))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Proof
