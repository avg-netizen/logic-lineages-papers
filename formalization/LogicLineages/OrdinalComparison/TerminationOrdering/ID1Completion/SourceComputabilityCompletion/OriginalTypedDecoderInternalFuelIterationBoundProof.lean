module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc emb zRelabel sucRelabel varBind nextTerm)
open InternalTagArithmeticSupportProof (natInduction)
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelIterationBoundSyntaxProof
open OriginalTypedDecoderInternalFuelIterationBoundCoreProof
open OriginalTypedDecoderInternalFuelIterationBoundStepProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem successorRow (H : Program 1) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (sufficientRow H count))) :
    Nonempty (Derivation body Gamma (sufficientRow H (suc count))) := by
  unfold sufficientRow
  apply actualFiniteUniversalIntroduction body alpha 2 Gamma
  let workCode : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let required : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let n := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 2)
  let A := WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required (suc n)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [sufficientRowRename] at hrow'
  obtain ⟨h⟩ := successorCore H n workCode required hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [sufficientBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

/-- Ordinary arithmetic induction, with the actual changing worklist and
its computed weight universally quantified INSIDE the induction invariant. -/
theorem allRows (H : Program 1) (count : OTerm alpha) :
    Nonempty (Derivation body Gamma (sufficientRow H count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := sufficientRow H (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,sufficientInstantiate,varBind] using
      (zeroRow (body := body) (Gamma := Gamma) H)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := successorRow (body := body) (Gamma := theta :: Gamma.map weaken)
      H (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,sufficientSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,sufficientInstantiate,varBind] using (Nonempty.intro h)

theorem sufficientFuel (H : Program 1) (workCode required count : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count))) :
    Nonempty (Derivation body Gamma (TerminatedWork H count workCode)) :=
  rowApply H count workCode required (allRows H count) hf hb

theorem actualOriginalTypedInternalSufficientFuel :
    OriginalTypedDecoderInternalFuelTargets.ActualOriginalTypedInternalSufficientFuel := by
  intro body H alpha workCode required count
  let A := WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required count
  have ha : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := sufficientFuel H workCode required count (andLeft ha) (andRight ha)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundProof
