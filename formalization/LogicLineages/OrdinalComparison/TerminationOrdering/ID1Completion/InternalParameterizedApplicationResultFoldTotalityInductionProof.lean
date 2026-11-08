module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationResultFoldTotality InternalParameterizedApplicationResultFoldTotalityTargets
open InternalParameterizedApplicationResultFoldTotalitySyntaxProof InternalParameterizedApplicationResultFoldTotalityBindingProof
open InternalParameterizedApplicationResultFoldTotalityOpeningProof
open InternalParameterizedApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalControlGraphChoiceProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalRecursionClosureLogicProof
open InternalSquareRootArithmeticSupportProof InternalApplicationValidityClosure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The actual arbitrary leaf Program supplies its output inside the calculus. -/
theorem leafHasOutput (guard leaf : Program 2) (combine : Program 5)
    (input parameter : OTerm α)
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z input parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine input parameter)) := by
  apply programCases leaf (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta out hj hl
  rw [hasCertifiedOutputRename]
  have hg' := renameInto hg j Delta hj
  simp only [graph2Rename,zRelabel] at hg'
  simp only [consTermRename,emptyRename] at hl
  apply hasCertifiedOutputIntro guard leaf combine out (input.relabel j) (parameter.relabel j)
  exact InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    guard leaf combine (input.relabel j) out (parameter.relabel j) hg' hl

/-- The actual arbitrary quinary callback supplies its output after both
certified children. Function comes before argument and the parameter is shared. -/
theorem applicationFromOutputs (guard leaf : Program 2) (combine : Program 5)
    (arrow d e fp ap fn arg parent functionOut argumentOut parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine argumentOut arg parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine parent parameter)) := by
  apply programCases combine
    (Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))) _
  intro β j Delta out hj hcomb
  rw [hasCertifiedOutputRename]
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [certifiedFoldPRename] at hf' ha'
  simp only [consTermRename,emptyRename] at hcomb
  apply hasCertifiedOutputIntro guard leaf combine out (parent.relabel j) (parameter.relabel j)
  exact InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
    guard leaf combine (parameter.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (functionOut.relabel j) (argumentOut.relabel j) out
    (andLeft hc') (andLeft (andRight hc')) (andLeft (andRight (andRight hc')))
    (andRight (andRight (andRight hc'))) hg' hf' ha' hcomb

/-- Both child witnesses are eliminated in their actual fresh-variable scopes. -/
theorem applicationFromChildExistence (guard leaf : Program 2) (combine : Program 5)
    (arrow d e fp ap fn arg parent parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine fn parameter)))
    (ha : Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine arg parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine parent parameter)) := by
  apply hasCertifiedOutputCases guard leaf combine fn parameter _ hf
  intro β j Delta functionOut hj hfn
  rw [hasCertifiedOutputRename]
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have ha' := renameInto ha j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [hasCertifiedOutputRename] at ha'
  apply hasCertifiedOutputCases guard leaf combine (arg.relabel j) (parameter.relabel j) _ ha'
  intro γ k E argumentOut hk harg
  rw [hasCertifiedOutputRename]
  have hc'' := renameInto hc' k E hk
  have hg'' := renameInto hg' k E hk
  have hfn' := renameInto hfn k E hk
  simp only [conjunctionRename,graph2Rename,graph4Rename] at hc''
  simp only [graph2Rename,sucRelabel,zRelabel] at hg''
  rw [certifiedFoldPRename] at hfn'
  exact applicationFromOutputs guard leaf combine ((arrow.relabel j).relabel k)
    ((d.relabel j).relabel k) ((e.relabel j).relabel k) ((fp.relabel j).relabel k)
    ((ap.relabel j).relabel k) ((fn.relabel j).relabel k) ((arg.relabel j).relabel k)
    ((parent.relabel j).relabel k) (functionOut.relabel k) argumentOut
    ((parameter.relabel j).relabel k) hc'' hg'' hfn' harg

/-- Actual opening acceptance reconstructs both original children, whose
payloads strictly decrease. No source validity or type membership is needed. -/
theorem acceptedHasOutput (guard leaf : Program 2) (combine : Program 5)
    (p input parameter : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload guard leaf combine p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine input parameter)) := by
  apply openingCases guard input parameter _ hg
  intro β j Delta payload arrow d e fp ap fn arg hj hc hparent hfn harg hfp hap hguard
  rw [hasCertifiedOutputRename]
  have hb' := renameInto hb j Delta hj
  have hr' := renameInto hr j Delta hj
  rw [belowPayloadRename] at hb'
  rw [graph1Rename] at hr'
  obtain ⟨hep⟩ := valueUnique InternalUnpair.right payload (p.relabel j)
    (Fin.cons (input.relabel j) Fin.elim0) hparent hr'
  obtain ⟨hfp⟩ := hfp
  obtain ⟨hap⟩ := hap
  have hf := belowPayloadApply guard leaf combine (p.relabel j) fp fn (parameter.relabel j)
    hb' ⟨orderRight fp hep hfp⟩ hfn
  have ha := belowPayloadApply guard leaf combine (p.relabel j) ap arg (parameter.relabel j)
    hb' ⟨orderRight ap hep hap⟩ harg
  exact applicationFromChildExistence guard leaf combine arrow d e fp ap fn arg
    (input.relabel j) (parameter.relabel j) hc hguard hf ha

/-- The existing normalized conjunction splits at exact ONE; rejection gives
its actual ZERO graph even when the arbitrary callback G is not Boolean. -/
theorem stepAtInput (guard leaf : Program 2) (combine : Program 5)
    (p input parameter : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload guard leaf combine p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine input parameter)) := by
  let accepted := graph2 (InternalParameterizedApplicationResultStack.openGuardP guard)
    (suc z) input parameter
  obtain ⟨hb⟩ := hb
  obtain ⟨hr⟩ := hr
  obtain ⟨hy⟩ := acceptedHasOutput (body := body) (Gamma := accepted :: Gamma)
    guard leaf combine p input parameter ⟨addHyp hb accepted⟩ ⟨addHyp hr accepted⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz : Nonempty (Derivation body (accepted.not :: Gamma)
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z input parameter)) :=
    InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
      (Fin.cons input (Fin.cons parameter Fin.elim0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := leafHasOutput (body := body) (Gamma := accepted.not :: Gamma)
    guard leaf combine input parameter hz
  exact ⟨disjunctionElimination (excludedMiddle accepted)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

/-- Bind every original packed input and parameter inside the payload step. -/
theorem payloadStep (guard leaf : Program 2) (combine : Program 5)
    (p : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload guard leaf combine p))) :
    Nonempty (Derivation body Gamma (atPayloadP guard leaf combine p)) := by
  apply atPayloadIntro guard leaf combine p
  let input : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let parameter : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let Delta := graph1 InternalUnpair.right (p.relabel Sum.inl) input ::
    Gamma.map (fun q => q.relabel Sum.inl)
  have hb' := renameInto hb (Sum.inl : α → α ⊕ Fin 2) Delta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowPayloadRename] at hb'
  obtain ⟨h⟩ := stepAtInput guard leaf combine (p.relabel Sum.inl) input parameter hb'
    (show Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (p.relabel Sum.inl) input)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- The existing internal strong-induction rule discharges the genuine step. -/
theorem actualOriginalParameterizedResultFoldPayloadTotality :
    ActualOriginalParameterizedResultFoldPayloadTotality := by
  intro body guard leaf combine α Gamma payload
  apply payloadInduction guard leaf combine payload
  intro β Delta p hb
  exact payloadStep guard leaf combine p hb

/-- Internally obtain the original input payload and instantiate the uniform
invariant. No successful run or output witness is supplied externally. -/
theorem certifiedOutputExists (guard leaf : Program 2) (combine : Program 5)
    (input parameter : OTerm α) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine input parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro β j Delta payload hj hr
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hr
  exact atPayloadApply guard leaf combine payload (input.relabel j) (parameter.relabel j)
    (actualOriginalParameterizedResultFoldPayloadTotality body guard leaf combine β Delta payload) hr

theorem actualOriginalParameterizedResultFoldCertifiedOutput :
    ActualOriginalParameterizedResultFoldCertifiedOutput := by
  intro body guard leaf combine α Gamma input parameter
  exact certifiedOutputExists guard leaf combine input parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityInductionProof
