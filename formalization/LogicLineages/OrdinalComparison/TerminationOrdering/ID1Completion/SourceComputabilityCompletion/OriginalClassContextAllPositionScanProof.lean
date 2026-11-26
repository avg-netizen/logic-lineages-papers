module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalOriginalOrderSyntaxProof InternalOriginalPairingOrderArithmeticProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalClassContextAllPositionObserver OriginalClassContextAllPositionScanSyntaxProof
open OriginalClassContextAllPositionScanSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (R : Program 2) (cutoff seed candidate parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (ltF cutoff z))) :
    Nonempty (Derivation body Delta (graph4 (positionTest R) (suc z) cutoff seed candidate parameter)) := by
  obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero (body := body) (Gamma := Delta) cutoff
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn hl)⟩

theorem zeroRow (R : Program 2) : Nonempty (Derivation body Delta (row R z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let seed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let candidate : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let cutoff : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := graph4 (scan R) (suc z) z seed candidate parameter ⊓ ltF cutoff z
  obtain ⟨h⟩ := zeroCore (body := body)
    (Delta := A :: Delta.map (fun p => p.relabel Sum.inl)) R cutoff seed candidate parameter
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succCore (R : Program 2) (count cutoff seed candidate parameter : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row R count)))
    (hs : Nonempty (Derivation body Delta (graph4 (scan R) (suc z) (suc count) seed candidate parameter)))
    (hl : Nonempty (Derivation body Delta (ltF cutoff (suc count)))) :
    Nonempty (Derivation body Delta (graph4 (positionTest R) (suc z) cutoff seed candidate parameter)) := by
  have hh := successorExposure R count seed candidate parameter hs
  apply weakCases cutoff count _ hl
  · exact rowApply R count cutoff seed candidate parameter
      (withHyp hrow (ltF cutoff count)) (withHyp (andLeft hh) (ltF cutoff count))
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact headTransport (positionTest R) (suc z) count cutoff
      (Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0)))
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩
      (withHyp (andRight hh) (eqn cutoff count))

theorem succRow (R : Program 2) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row R count))) :
    Nonempty (Derivation body Delta (row R (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let seed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let candidate : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let cutoff : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let A := graph4 (scan R) (suc z) (suc c) seed candidate parameter ⊓ ltF cutoff (suc c)
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore R c cutoff seed candidate parameter hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (R : Program 2) (count : OTerm alpha) :
    Nonempty (Derivation body Delta (row R count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row R (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) R)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      R (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

/-- Every actually in-range test is exposed by the literal accepted scan.
This is an arithmetic derivation, not a reflection of native evaluation. -/
theorem exposeAt (R : Program 2) (bound cutoff seed candidate parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph4 (scan R) InternalOriginalStepGuard.one bound seed candidate parameter)))
    (hlt : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff bound))) :
    Nonempty (Derivation body Delta
      (graph4 (positionTest R) InternalOriginalStepGuard.one cutoff seed candidate parameter)) :=
  rowApply R bound cutoff seed candidate parameter (allRows R bound) hs hlt

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanProof.exposeAt
