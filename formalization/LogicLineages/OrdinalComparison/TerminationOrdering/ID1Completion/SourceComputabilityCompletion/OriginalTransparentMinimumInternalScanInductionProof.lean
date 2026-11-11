module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumStepGraphsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentMinimum OriginalTransparentMinimumInternalScanSyntaxProof
open OriginalTransparentMinimumInternalScanSupportProof OriginalTransparentMinimumStepGraphsProof
open InternalGraphComposition InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof InternalPositiveUnfoldingSupportProof
open InternalSourceInversionSupportProof InternalLeastNumberProof InternalControlGraphChoiceProof
open InternalClosedPrograms InternalClosedProgramsBindingProof SourceComputabilityFormulaSupportProof
open InternalRawListRecursionSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (Q : Program 3) (bound seed parameter out earlier : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (scanRow Q bound)))
    (hr : Nonempty (Derivation body Gamma (graph3 (scan Q) out bound seed parameter))) :
    Nonempty (Derivation body Gamma (resultFormula Q bound seed parameter out earlier)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (scanBody Q bound)
    (fun i => emb (![seed,parameter,out,earlier] i)) hrow
  rw [bodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h hr⟩

theorem zeroCore (Q : Program 3) (seed parameter out earlier : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph3 (scan Q) out z seed parameter))) :
    Nonempty (Derivation body Gamma (resultFormula Q z seed parameter out earlier)) := by
  have hz : Nonempty (Derivation body Gamma (graph3 (scan Q) z z seed parameter)) := by
    apply recursionZeroValue (InternalAcceptance.constantZero 2) (scanStep Q) z
      (Fin.cons seed (Fin.cons parameter Fin.elim0))
    apply compositionValue .zero Fin.elim0 z _ Fin.elim0 (zeroValue Fin.elim0)
    intro i
    exact Fin.elim0 i
  have he := valueUnique (scan Q) z out (Fin.cons z (Fin.cons seed (Fin.cons parameter Fin.elim0))) hz hr
  exact resultTransport Q z seed parameter earlier z out he (resultZero Q seed parameter earlier)

theorem zeroRow (Q : Program 3) : Nonempty (Derivation body Gamma (scanRow Q (z : OTerm α))) := by
  unfold scanRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let seed : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let parameter : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let earlier : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := graph3 (scan Q) out z seed parameter
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) Q seed parameter out earlier
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [scanBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem successorResult (Q : Program 3) (bound seed parameter previous out earlier : OTerm α)
    (hi : Nonempty (Derivation body Gamma (resultFormula Q bound seed parameter previous earlier)))
    (hp : Nonempty (Derivation body Gamma (graph3 (scan Q) previous bound seed parameter)))
    (hr : Nonempty (Derivation body Gamma (graph3 (scan Q) out (suc bound) seed parameter))) :
    Nonempty (Derivation body Gamma (resultFormula Q (suc bound) seed parameter out earlier)) := by
  obtain ⟨hi⟩ := hi
  obtain ⟨hp⟩ := hp
  obtain ⟨hr⟩ := hr
  let L := ltF previous bound
  let H := graph3 Q (suc z) seed bound parameter
  have hl : Nonempty (Derivation body (L :: Gamma)
      (resultFormula Q (suc bound) seed parameter out earlier)) := by
    have hs := stepRetained Q bound previous seed parameter
      (body := body) (Delta := L :: Gamma) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hc := recursionNext (InternalAcceptance.constantZero 2) (scanStep Q) previous previous bound
      (Fin.cons seed (Fin.cons parameter Fin.elim0)) ⟨addHyp hp _⟩ hs
    have he := valueUnique (scan Q) previous out
      (Fin.cons (suc bound) (Fin.cons seed (Fin.cons parameter Fin.elim0))) hc ⟨addHyp hr _⟩
    exact resultTransport Q (suc bound) seed parameter earlier previous out he
      (resultRetained Q bound seed parameter previous earlier ⟨addHyp hi _⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hh : Nonempty (Derivation body (H :: L.not :: Gamma)
      (resultFormula Q (suc bound) seed parameter out earlier)) := by
    have hs := stepHit Q bound previous seed parameter
      (body := body) (Delta := H :: L.not :: Gamma)
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hc := recursionNext (InternalAcceptance.constantZero 2) (scanStep Q) bound previous bound
      (Fin.cons seed (Fin.cons parameter Fin.elim0)) ⟨addHyp (addHyp hp _) _⟩ hs
    have he := valueUnique (scan Q) bound out
      (Fin.cons (suc bound) (Fin.cons seed (Fin.cons parameter Fin.elim0))) hc ⟨addHyp (addHyp hr _) _⟩
    exact resultTransport Q (suc bound) seed parameter earlier bound out he
      (resultHit Q bound seed parameter previous earlier ⟨addHyp (addHyp hi _) _⟩
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hm : Nonempty (Derivation body (H.not :: L.not :: Gamma)
      (resultFormula Q (suc bound) seed parameter out earlier)) := by
    have hs := stepMiss Q bound previous seed parameter
      (body := body) (Delta := H.not :: L.not :: Gamma)
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hc := recursionNext (InternalAcceptance.constantZero 2) (scanStep Q) (suc bound) previous bound
      (Fin.cons seed (Fin.cons parameter Fin.elim0)) ⟨addHyp (addHyp hp _) _⟩ hs
    have he := valueUnique (scan Q) (suc bound) out
      (Fin.cons (suc bound) (Fin.cons seed (Fin.cons parameter Fin.elim0))) hc ⟨addHyp (addHyp hr _) _⟩
    exact resultTransport Q (suc bound) seed parameter earlier (suc bound) out he
      (resultMiss Q bound seed parameter previous earlier ⟨addHyp (addHyp hi _) _⟩
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hl⟩ := hl
  obtain ⟨hh⟩ := hh
  obtain ⟨hm⟩ := hm
  exact ⟨disjunctionElimination (excludedMiddle L)
    (Derivation.implicationIntroduction hl)
    (Derivation.implicationIntroduction (disjunctionElimination (excludedMiddle H)
      (Derivation.implicationIntroduction hh) (Derivation.implicationIntroduction hm)))⟩

theorem succCore (Q : Program 3) (bound seed parameter out earlier : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (scanRow Q bound)))
    (hr : Nonempty (Derivation body Gamma (graph3 (scan Q) out (suc bound) seed parameter))) :
    Nonempty (Derivation body Gamma (resultFormula Q (suc bound) seed parameter out earlier)) := by
  apply programCases (scan Q) (Fin.cons bound (Fin.cons seed (Fin.cons parameter Fin.elim0))) _
  intro β j Delta previous hj hp
  rw [resultRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hp
  have hrow' := renameInto hrow j Delta hj
  rw [rowRename] at hrow'
  have hr' := renameInto hr j Delta hj
  simp only [graphRename,sucRelabel] at hr'
  exact successorResult Q (bound.relabel j) (seed.relabel j) (parameter.relabel j)
    previous (out.relabel j) (earlier.relabel j)
    (rowApply Q (bound.relabel j) (seed.relabel j) (parameter.relabel j) previous (earlier.relabel j) hrow' hp)
    hp hr'

theorem succRow (Q : Program 3) (bound : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (scanRow Q bound))) :
    Nonempty (Derivation body Gamma (scanRow Q (suc bound))) := by
  unfold scanRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let seed : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let parameter : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let earlier : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let c := bound.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := graph3 (scan Q) out (suc c) seed parameter
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨d⟩ := succCore Q c seed parameter out earlier hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [scanBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- PA induction in the original full-language calculus. No native theorem
or external induction over standard natural numbers supplies this derivation. -/
theorem allRows (Q : Program 3) (bound : OTerm α) : Nonempty (Derivation body Gamma (scanRow Q bound)) := by
  let theta : Formula (α ⊕ Fin 1) := scanRow Q (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,OriginalTransparentMinimumInternalScanSyntaxProof.rowInstantiate,varBind]
      using (zeroRow (body := body) (Gamma := Gamma) Q)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      Q (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,OriginalTransparentMinimumInternalScanSyntaxProof.rowSuccessor,
      nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb bound) (natInduction theta hz hs)
  simpa only [theta,OriginalTransparentMinimumInternalScanSyntaxProof.rowInstantiate,varBind]
    using (Nonempty.intro h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalScanInductionProof
