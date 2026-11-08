module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldTargets
open InternalParameterizedCanonicalResultFoldSyntaxProof InternalParameterizedCanonicalResultFoldBindingProof
open InternalParameterizedCanonicalResultFoldLeafProof InternalParameterizedCanonicalResultFoldApplicationProof
open InternalParameterizedCanonicalResultFoldOpeningProof InternalApplicationValidityClosure
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalControlGraphChoiceProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalRecursionClosureLogicProof
open InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationFromChildExistence (data : Data)
    (arrow d e fp ap fn arg parent parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard data) (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (hasCertifiedOutput data fn arrow parameter)))
    (ha : Nonempty (Derivation body Gamma (hasCertifiedOutput data arg d parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data parent e parameter)) := by
  apply hasCertifiedOutputCases data fn arrow parameter _ hf
  intro β j Delta functionOut hj hfn
  rw [hasCertifiedOutputRename]
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have ha' := renameInto ha j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [hasCertifiedOutputRename] at ha'
  apply hasCertifiedOutputCases data (arg.relabel j) (d.relabel j) (parameter.relabel j) _ ha'
  intro γ k E argumentOut hk harg
  rw [hasCertifiedOutputRename]
  have hc'' := renameInto hc' k E hk
  have hg'' := renameInto hg' k E hk
  have hfn' := renameInto hfn k E hk
  simp only [conjunctionRename,graph2Rename,graph4Rename] at hc''
  simp only [graph2Rename,sucRelabel,zRelabel] at hg''
  rw [certifiedOutputRename] at hfn'
  exact applicationHasOutput data ((arrow.relabel j).relabel k)
    ((d.relabel j).relabel k) ((e.relabel j).relabel k) ((fp.relabel j).relabel k)
    ((ap.relabel j).relabel k) ((fn.relabel j).relabel k) ((arg.relabel j).relabel k)
    ((parent.relabel j).relabel k) (functionOut.relabel k) argumentOut
    ((parameter.relabel j).relabel k) hc'' hg'' hfn' harg

theorem openingHasOutput (data : Data)
    (p input typ parameter payload arrow d e fp ap fn arg : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises data input typ parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap arg)))
    (hfl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess fp payload)))
    (hal : Nonempty (Derivation body Gamma (InternalLessThan.strictLess ap payload)))
    (hg : Nonempty (Derivation body Gamma (graph2 (rootGuard data) (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)) := by
  have hv := rootGuardRecover data arrow d e fp ap fn arg input parameter hc hg
  obtain ⟨hep⟩ := valueUnique InternalUnpair.right payload p (Fin.cons input Fin.elim0) hpr hr
  obtain ⟨hfl⟩ := hfl
  obtain ⟨hal⟩ := hal
  have hf := belowPayloadApply data p fp fn arrow parameter hb ⟨orderRight fp hep hfl⟩ hfr
    (andIntro (andLeft (andRight hv))
      (pairLeft fn arrow fp (andLeft (andRight hc))))
  have ha := belowPayloadApply data p ap arg d parameter hb ⟨orderRight ap hep hal⟩ har
    (andIntro (andLeft (andRight (andRight hv)))
      (pairLeft arg d ap (andLeft (andRight (andRight hc)))))
  have hl := InternalCanonicalResultFoldInvariantApplicationSupportProof.packedLeft
    d e fp ap input (andRight (andRight (andRight hc)))
  have he := valueUnique InternalUnpair.left e typ (Fin.cons input Fin.elim0) hl (andRight hs)
  exact hasOutputTagTransport data input e typ parameter he
    (applicationFromChildExistence data arrow d e fp ap fn arg input parameter hc hg hf ha)

/-- Original constructor and strict child payload graphs come from actual
opening acceptance inside the calculus, without semantic decoding premises. -/
theorem acceptedHasOutput (data : Data) (p input typ parameter : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises data input typ parameter)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard data))
        (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)) := by
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (rootGuard data) input parameter _ hg
  intro β j Delta payload arrow d e fp ap fn arg hj hc hpr hfr har hfl hal hguard
  rw [hasCertifiedOutputRename]
  have hb' := renameInto hb j Delta hj
  have hr' := renameInto hr j Delta hj
  have hs' := renameInto hs j Delta hj
  rw [belowPayloadRename] at hb'
  rw [graph1Rename] at hr'
  rw [sourcePremisesRename] at hs'
  exact openingHasOutput data (p.relabel j) (input.relabel j) (typ.relabel j)
    (parameter.relabel j) payload arrow d e fp ap fn arg hb' hr' hs'
    hc hpr hfr har hfl hal hguard

theorem stepAtInput (data : Data) (p input typ parameter : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises data input typ parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)) := by
  let accepted := graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard data))
    (suc z) input parameter
  obtain ⟨hb⟩ := hb
  obtain ⟨hr⟩ := hr
  obtain ⟨hs⟩ := hs
  obtain ⟨hy⟩ := acceptedHasOutput (body := body) (Gamma := accepted :: Gamma)
    data p input typ parameter ⟨addHyp hb accepted⟩ ⟨addHyp hr accepted⟩ ⟨addHyp hs accepted⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz : Nonempty (Derivation body (accepted.not :: Gamma)
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP (rootGuard data)) z input parameter)) :=
    InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
      (Fin.cons input (Fin.cons parameter Fin.elim0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := leafHasOutput (body := body) (Gamma := accepted.not :: Gamma)
    data input typ parameter ⟨addHyp hs accepted.not⟩ hz
  exact ⟨disjunctionElimination (excludedMiddle accepted)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

theorem payloadStep (data : Data) (p : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data p))) :
    Nonempty (Derivation body Gamma (atPayload data p)) := by
  apply atPayloadIntro data p
  let input : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let typ : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let parameter : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let Delta := sourcePremises data input typ parameter ::
    graph1 InternalUnpair.right (p.relabel Sum.inl) input :: Gamma.map (fun q => q.relabel Sum.inl)
  have hb' := renameInto hb (Sum.inl : α → α ⊕ Fin 3) Delta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)))
  rw [belowPayloadRename] at hb'
  obtain ⟨h⟩ := stepAtInput data (p.relabel Sum.inl) input typ parameter hb'
    (show Nonempty (Derivation body Delta (graph1 InternalUnpair.right (p.relabel Sum.inl) input)) from
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    (show Nonempty (Derivation body Delta (sourcePremises data input typ parameter)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

theorem payloadInvariant (data : Data) (payload : OTerm α) :
    Nonempty (Derivation body Gamma (atPayload data payload)) := by
  apply payloadInduction data payload
  intro β Delta p hb
  exact payloadStep data p hb

theorem certifiedOutputExists (data : Data) (input typ parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (sourcePremises data input typ parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro β j Delta payload hj hr
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hr
  have hs' := renameInto hs j Delta hj
  rw [sourcePremisesRename] at hs'
  exact atPayloadApply data payload (input.relabel j) (typ.relabel j) (parameter.relabel j)
    (payloadInvariant data payload) hr hs'

theorem actualParameterizedCanonicalFoldCertifiedOutput : ActualParameterizedCanonicalFoldCertifiedOutput := by
  intro body data α Gamma input typ parameter
  obtain ⟨h⟩ := certifiedOutputExists (body := body)
    (Gamma := sourcePremises data input typ parameter :: Gamma) data input typ parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldInductionProof
