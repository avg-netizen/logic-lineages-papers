module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnSubst eqnRelabel zSubst zRelabel sucRelabel bindEmbedding bindTerm nextEmbedding nextTerm)
open InternalTagArithmeticSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceSupportProof
open OriginalTypedDecoderInternalBranchProof (orCases)
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (varBind)
open OriginalUniverseDecoderInternalFuelNumericSupportProof
open OriginalUniverseDecoderInternalFuelStepProof
open OriginalUniverseDecoderInternalFuelInclusionSyntaxProof OriginalUniverseDecoderInternalFuelInclusionStepProof
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem rowApply (H : Program 1) (M contextWindow : Program 2) (count initial out c : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (inclusionRow H M contextWindow count)))
    (hr : Nonempty (Derivation body Gamma
      (graph3 (OriginalUniverseDecoder.iterate H M contextWindow) out count initial c))) :
    Nonempty (Derivation body Gamma (runResult H out count initial)) := by
  have h := actualFiniteUniversalElimination body alpha 3 Gamma (inclusionBody H M contextWindow count)
    (fun i => emb (![initial,out,c] i)) hrow
  rw [inclusionBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h hr⟩

theorem zeroCore (H : Program 1) (M contextWindow : Program 2) (initial out c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma
      (graph3 (OriginalUniverseDecoder.iterate H M contextWindow) out z initial c))) :
    Nonempty (Derivation body Gamma (runResult H out z initial)) := by
  obtain ⟨he⟩ := repeatZeroRecover (OriginalUniverseDecoder.transition H M contextWindow) out initial c hr
  obtain ⟨ht⟩ := outputTransport (OriginalTypedDecoder.iterate H) initial out
    (Fin.cons z (Fin.cons initial Fin.elim0)) ⟨symm he⟩
    (InternalNumericIterationSupportProof.repeatZeroValue (OriginalTypedDecoder.transition H) initial)
  exact ⟨orRight ht⟩

theorem zeroRow (H : Program 1) (M contextWindow : Program 2) :
    Nonempty (Derivation body Gamma (inclusionRow H M contextWindow (z : OTerm alpha))) := by
  unfold inclusionRow
  apply actualFiniteUniversalIntroduction body alpha 3 Gamma
  let initial : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := graph3 (OriginalUniverseDecoder.iterate H M contextWindow) out z initial c
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) H M contextWindow initial out c
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [inclusionBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem successorCore (H : Program 1) (M contextWindow : Program 2)
    (count initial out c : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (inclusionRow H M contextWindow count)))
    (hr : Nonempty (Derivation body Gamma
      (graph3 (OriginalUniverseDecoder.iterate H M contextWindow) out (suc count) initial c))) :
    Nonempty (Derivation body Gamma (runResult H out (suc count) initial)) := by
  apply programCases (OriginalUniverseDecoder.iterate H M contextWindow)
    (Fin.cons count (Fin.cons initial (Fin.cons c Fin.elim0))) _
  intro beta j Delta previous hj hp
  simp only [runResultRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hp
  have hrow' := renameInto hrow j Delta hj
  rw [inclusionRowRename] at hrow'
  have hr' := renameInto hr j Delta hj
  simp only [graph3Rename,sucRelabel] at hr'
  have hs := repeatSuccRecover (OriginalUniverseDecoder.transition H M contextWindow)
    (count.relabel j) previous (out.relabel j) (initial.relabel j) (c.relabel j) hp hr'
  have hi := rowApply H M contextWindow (count.relabel j) (initial.relabel j) previous
    (c.relabel j) hrow' hp
  apply orCases hi
  · let Z := equal previous z
    have hz : Nonempty (Derivation body (Z :: Delta) (eqn previous z)) := by
      rw [← equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hs0 := headTransport (OriginalUniverseDecoder.transition H M contextWindow)
      (out.relabel j) previous z (Fin.cons (c.relabel j) Fin.elim0) hz (withHyp hs Z)
    have he := valueUnique (OriginalUniverseDecoder.transition H M contextWindow)
      (out.relabel j) z (Fin.cons z (Fin.cons (c.relabel j) Fin.elim0)) hs0
      (failureFixed H M contextWindow (c.relabel j))
    have heq : Nonempty (Derivation body (Z :: Delta) (equal (out.relabel j) z)) := by
      simpa only [equalEqn] using he
    obtain ⟨heq⟩ := heq
    exact ⟨orLeft heq⟩
  · let T := graph2 (OriginalTypedDecoder.iterate H) previous (count.relabel j) (initial.relabel j)
    have ht : Nonempty (Derivation body (T :: Delta) T) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hstep := stepRefinement H M contextWindow (out.relabel j) previous (c.relabel j) (withHyp hs T)
    apply orCases hstep
    · have hz : Derivation body (equal (out.relabel j) z :: T :: Delta) (equal (out.relabel j) z) :=
        Derivation.hypothesis List.mem_cons_self
      exact ⟨orLeft hz⟩
    · let S := graph1 (OriginalTypedDecoder.transition H) (out.relabel j) previous
      have hs' : Nonempty (Derivation body (S :: T :: Delta) S) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hn⟩ := InternalNumericIterationSupportProof.repeatSuccValue
        (OriginalTypedDecoder.transition H) (count.relabel j) previous
        (out.relabel j) (initial.relabel j) (withHyp ht S) hs'
      exact ⟨orRight hn⟩

theorem successorRow (H : Program 1) (M contextWindow : Program 2) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (inclusionRow H M contextWindow count))) :
    Nonempty (Derivation body Gamma (inclusionRow H M contextWindow (suc count))) := by
  unfold inclusionRow
  apply actualFiniteUniversalIntroduction body alpha 3 Gamma
  let initial : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let n := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let A := graph3 (OriginalUniverseDecoder.iterate H M contextWindow) out (suc n) initial c
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [inclusionRowRename] at hrow'
  obtain ⟨d⟩ := successorCore H M contextWindow n initial out c hrow'
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [inclusionBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Arithmetic induction in the unchanged original numeric count. Guard
failure stays failure; every nonfailure guarded output has an actual typed
execution with exactly the same initial raw state and count. -/
theorem allRows (H : Program 1) (M contextWindow : Program 2) (count : OTerm alpha) :
    Nonempty (Derivation body Gamma (inclusionRow H M contextWindow count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := inclusionRow H M contextWindow (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,inclusionInstantiate,varBind] using
      (zeroRow (body := body) (Gamma := Gamma) H M contextWindow)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := successorRow (body := body) (Gamma := theta :: Gamma.map weaken)
      H M contextWindow (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,inclusionSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,inclusionInstantiate,varBind] using (Nonempty.intro h)

theorem runRefinement (H : Program 1) (M contextWindow : Program 2) (out count initial c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma
      (graph3 (OriginalUniverseDecoder.iterate H M contextWindow) out count initial c))) :
    Nonempty (Derivation body Gamma (runResult H out count initial)) :=
  rowApply H M contextWindow count initial out c (allRows H M contextWindow count) hr

theorem sameFuelAccepted (H : Program 1) (M contextWindow : Program 2) (count initial c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma
      (graph3 (OriginalUniverseDecoder.iterate H M contextWindow) (numeral 2) count initial c))) :
    Nonempty (Derivation body Gamma (graph2 (OriginalTypedDecoder.iterate H) (numeral 2) count initial)) := by
  apply orCases (runRefinement H M contextWindow (numeral 2) count initial c hr)
  · have hz : Derivation body (equal (numeral 2) z :: Gamma) (eqn (suc (suc z)) z) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact ⟨Derivation.explosion (sucNeZeroApply hz)⟩
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem actualOriginalUniverseInternalSameFuelTypedAcceptance :
    OriginalUniverseDecoderInternalFuelTargets.ActualOriginalUniverseInternalSameFuelTypedAcceptance := by
  intro body H M contextWindow alpha count initial c
  obtain ⟨h⟩ := sameFuelAccepted (body := body)
    (Gamma := [graph3 (OriginalUniverseDecoder.iterate H M contextWindow) (numeral 2) count initial c])
    H M contextWindow count initial c ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionProof
