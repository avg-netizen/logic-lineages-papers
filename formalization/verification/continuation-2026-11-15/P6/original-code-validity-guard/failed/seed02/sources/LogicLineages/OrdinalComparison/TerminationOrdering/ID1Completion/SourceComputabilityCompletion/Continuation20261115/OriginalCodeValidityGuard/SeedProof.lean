module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedProof
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
open Continuation20261115.OriginalCodeDecoderTable Continuation20261115.OriginalCodeValidityGuard.SeedSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open Continuation20261115.OriginalCodeValidityGuard.SeedCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 2 Delta
  let output : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let index : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let A := fields z output index
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    output index ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count))) :
    Nonempty (Derivation body Delta (row (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 2 Delta
  let output : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let index : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 2)
  let A := fields (suc c) output index
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
  have hrow' := InternalGraphCompositionFunctionalityProof.renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore c output index hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
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

theorem zerosLookup (count output index : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (Below index count)))
    (ho : Nonempty (Derivation body Delta (graph1 OriginalCodeDecoderTable.zeros output count))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup z index output)) :=
  rowApply count output index (allRows count) (andIntro hb ho)

 theorem seedLookup (bound output index : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (Below index (suc bound))))
    (ho : Nonempty (Derivation body Delta (graph1 OriginalCodeDecoderTable.seed output bound))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup z index output)) := by
  have hs := OriginalCodeDecoderTable.SupportProof.succProjection (body := body) (Delta := Delta)
    (0 : Fin 1) (Fin.cons bound Fin.elim0)
  have hz := InternalApplicationCertificateConstructorsSupportProof.unaryRecover
    OriginalCodeDecoderTable.zeros (OriginalRawSyntaxTransport.succOf (.projection 0))
    output (suc bound) (Fin.cons bound Fin.elim0) ho hs
  exact zerosLookup (suc bound) output index hb hz

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedProof
