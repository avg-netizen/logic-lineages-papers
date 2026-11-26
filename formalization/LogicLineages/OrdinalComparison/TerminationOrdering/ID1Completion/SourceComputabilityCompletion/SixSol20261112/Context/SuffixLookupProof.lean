module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc emb varBind nextTerm zRelabel sucRelabel)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open SuffixLookupSyntaxProof SuffixLookupCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalRawListRecursion.lookup
  InternalApplicationValidityStackAppend.append OriginalContextInsertion.length

theorem zeroRow : Nonempty (Derivation body Delta (row (z : OTerm alpha))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 5 Delta
  let front : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let suffix : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let joined : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let cutoff : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let value : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := fields z front suffix joined
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
  obtain ⟨h⟩ := zeroCore front suffix joined cutoff value
    (body := body) (Delta := Theta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem successorRow (count : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row count))) :
    Nonempty (Derivation body Delta (row (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 5 Delta
  let front : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let suffix : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let joined : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let cutoff : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let value : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
  let A := fields (suc c) front suffix joined
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
  have hi' := renameInto hi Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [SuffixLookupSyntaxProof.rowRename] at hi'
  obtain ⟨h⟩ := successorCore c front suffix joined cutoff value hi'
    (show Nonempty (Derivation body Theta A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (count : OTerm alpha) : Nonempty (Derivation body Delta (row count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,SuffixLookupSyntaxProof.rowInstantiate,varBind] using
      (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := successorRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,SuffixLookupSyntaxProof.rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count)
    (InternalTagArithmeticSupportProof.natInduction theta hz hs)
  simpa only [theta,SuffixLookupSyntaxProof.rowInstantiate,varBind] using (Nonempty.intro h)

theorem actualUnboundedSuffixLookup : SuffixLookupTargets.ActualUnboundedSuffixLookup := by
  intro body alpha Delta count front suffix joined cutoff value hl ha
  exact rowApply count front suffix joined cutoff value (allRows count) (andIntro hl ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupProof.actualUnboundedSuffixLookup
