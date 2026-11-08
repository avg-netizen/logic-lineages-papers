module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalBoundedDescentNormalizer InternalBoundedDescentNormalizerSyntaxProof
open InternalBoundedDescentNormalizerSupportProof InternalBoundedDescentNormalizerStepProof
open InternalNumericIteration InternalNumericIterationSyntaxProof InternalNumericIterationSupportProof
open InternalNumericIterationFixedPointProof InternalNumericIterationProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalSquareRootArithmeticSupportProof InternalUnpairReverseBoundsArithmeticProof
open InternalLeastNumberProof InternalSourceInversionSupportProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (R V : Program 1) (count input out typ : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow R V count)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (transition R V) out count input))) :
    Nonempty (Derivation body Gamma (resultFormula R V count input out typ)) := by
  have h := actualFiniteUniversalElimination body α 3 Gamma (iterationBody R V count)
    (fun i => emb (![input,out,typ] i)) hrow
  rw [bodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h hr⟩

theorem zeroCore (R V : Program 1) (input out typ : OTerm α)
    (hr : Nonempty (Derivation body Gamma (repeatGraph (transition R V) out z input))) :
    Nonempty (Derivation body Gamma (resultFormula R V z input out typ)) := by
  obtain ⟨he⟩ := repeatZeroRecover (transition R V) out input hr
  have hb : Derivation body Gamma (atMost out input) := equalToNext he
  have hv : Nonempty (Derivation body (validGraph V input :: Gamma) (validGraph V out)) :=
    unaryInput V (suc z) input out ⟨symm (addHyp he _)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hl : Nonempty (Derivation body (leftGraph typ input :: Gamma) (leftGraph typ out)) :=
    unaryInput InternalUnpair.left typ input out ⟨symm (addHyp he _)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf : Nonempty (Derivation body (atMost input z :: Gamma) (transitionGraph R V out out)) := by
    obtain ⟨hi⟩ := atMostZero (body := body) (Gamma := atMost input z :: Gamma) input
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact fixedTransport R V z out ⟨symm (trans (addHyp he _) hi)⟩
      (InternalBoundedDescentNormalizerStepProof.zeroValue R V)
  obtain ⟨hv⟩ := hv
  obtain ⟨hl⟩ := hl
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.conjunctionIntroduction hb
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hv)
      (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hl)
        (Derivation.implicationIntroduction hf)))⟩

theorem zeroRow (R V : Program 1) :
    Nonempty (Derivation body Gamma (iterationRow R V (z : OTerm α))) := by
  unfold iterationRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let input : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let out : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let typ : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let A := repeatGraph (transition R V) out z input
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) R V input out typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [iterationBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- The first transition either stays put, where the existing fixed-point
iteration theorem applies, or strictly decreases the symbolic fuel bound. -/
theorem successorFixed (R V : Program 1) (count input next out : OTerm α)
    (ht : Nonempty (Derivation body Gamma (transitionGraph R V next input)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (transition R V) out count next)))
    (hi : Nonempty (Derivation body Gamma
      ((atMost next count).imp (transitionGraph R V out out))))
    (hb : Nonempty (Derivation body Gamma (atMost input (suc count)))) :
    Nonempty (Derivation body Gamma (transitionGraph R V out out)) := by
  obtain ⟨hs⟩ := stepSplit R V next input ht
  obtain ⟨ht⟩ := ht
  obtain ⟨hr⟩ := hr
  obtain ⟨hi⟩ := hi
  obtain ⟨hb⟩ := hb
  have he : Nonempty (Derivation body (eqn next input :: Gamma) (transitionGraph R V out out)) := by
    have hf := headTransport (transition R V) next input next Fin.elim0
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ ⟨addHyp ht _⟩
    exact repeatFixedResult R V count next out hf ⟨addHyp hr _⟩
  have hl : Nonempty (Derivation body (ltF next input :: Gamma) (transitionGraph R V out out)) := by
    obtain ⟨hbound⟩ := strictWeakTrans (body := body) (Gamma := ltF next input :: Gamma)
      next input (suc count) ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp hb _⟩
    exact ⟨Derivation.implicationElimination (addHyp hi _) hbound⟩
  obtain ⟨he⟩ := he
  obtain ⟨hl⟩ := hl
  exact ⟨disjunctionElimination hs (Derivation.implicationIntroduction he)
    (Derivation.implicationIntroduction hl)⟩

theorem successorResult (R V : Program 1) (count input next out typ : OTerm α)
    (ht : Nonempty (Derivation body Gamma (transitionGraph R V next input)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (transition R V) out count next)))
    (hi : Nonempty (Derivation body Gamma (resultFormula R V count next out typ))) :
    Nonempty (Derivation body Gamma (resultFormula R V (suc count) input out typ)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨ht⟩ := ht
  obtain ⟨hr⟩ := hr
  obtain ⟨hb⟩ := weakTrans out next input ⟨Derivation.conjunctionLeft hi⟩
    (boundOfSplit next input (stepSplit R V next input ⟨ht⟩))
  have hv : Nonempty (Derivation body (validGraph V input :: Gamma) (validGraph V out)) := by
    obtain ⟨hn⟩ := stepValid R V next input ⟨addHyp ht _⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationElimination
      (addHyp (Derivation.conjunctionLeft (Derivation.conjunctionRight hi)) _) hn⟩
  have hl : Nonempty (Derivation body (leftGraph typ input :: Gamma) (leftGraph typ out)) := by
    obtain ⟨hn⟩ := stepLeft R V next input typ ⟨addHyp ht _⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationElimination
      (addHyp (Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hi))) _) hn⟩
  have hf : Nonempty (Derivation body (atMost input (suc count) :: Gamma)
      (transitionGraph R V out out)) :=
    successorFixed R V count input next out ⟨addHyp ht _⟩ ⟨addHyp hr _⟩
      ⟨addHyp (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hi))) _⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hv⟩ := hv
  obtain ⟨hl⟩ := hl
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.conjunctionIntroduction hb
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hv)
      (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hl)
        (Derivation.implicationIntroduction hf)))⟩

theorem succCore (R V : Program 1) (count input out typ : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow R V count)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (transition R V) out (suc count) input))) :
    Nonempty (Derivation body Gamma (resultFormula R V (suc count) input out typ)) := by
  apply programCases (transition R V) (Fin.cons input Fin.elim0) _
  intro β j Delta next hj ht
  rw [resultRename,sucRelabel]
  simp only [consTermRename,emptyRename] at ht
  have hrow' := renameInto hrow j Delta hj
  rw [rowRename] at hrow'
  have hr' := renameInto hr j Delta hj
  simp only [repeatRename,sucRelabel] at hr'
  have htail := frontSuccForward (transition R V) (count.relabel j) (out.relabel j)
    (input.relabel j) next ht hr'
  exact successorResult R V (count.relabel j) (input.relabel j) next (out.relabel j) (typ.relabel j)
    ht htail (rowApply R V (count.relabel j) next (out.relabel j) (typ.relabel j) hrow' htail)

theorem succRow (R V : Program 1) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow R V count))) :
    Nonempty (Derivation body Gamma (iterationRow R V (suc count))) := by
  unfold iterationRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let input : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let out : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let typ : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let c := count.relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := repeatGraph (transition R V) out (suc c) input
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨d⟩ := succCore R V c input out typ hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [iterationBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Full-language PA induction is applied inside the unchanged calculus.
There is no external natural-number induction or semantic reflection step. -/
theorem allRows (R V : Program 1) (count : OTerm α) :
    Nonempty (Derivation body Gamma (iterationRow R V count)) := by
  let theta : Formula (α ⊕ Fin 1) := iterationRow R V (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,InternalBoundedDescentNormalizerSyntaxProof.rowInstantiate,varBind] using
      (zeroRow (body := body) (Gamma := Gamma) R V)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      R V (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,InternalBoundedDescentNormalizerSyntaxProof.rowSuccessor,
      nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,InternalBoundedDescentNormalizerSyntaxProof.rowInstantiate,varBind] using
    (Nonempty.intro h)

theorem repeatResult (R V : Program 1) (count input out typ : OTerm α)
    (hr : Nonempty (Derivation body Gamma (repeatGraph (transition R V) out count input))) :
    Nonempty (Derivation body Gamma (resultFormula R V count input out typ)) :=
  rowApply R V count input out typ (allRows R V count) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerInductionProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerInductionProof
