module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph 
open InternalCanonicalResultFoldInvariant InternalCanonicalResultFoldInvariantTargets
open InternalCanonicalResultFoldInvariantSyntaxProof InternalCanonicalResultFoldInvariantBindingProof
open InternalCanonicalResultFoldInvariantLeafProof InternalCanonicalResultFoldInvariantApplicationProof
open InternalCanonicalResultFoldOpening InternalCanonicalResultFoldOpeningProof
open InternalCanonicalResultFoldOpeningSyntaxProof InternalApplicationValidityClosure
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalControlGraphChoiceProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalRecursionClosureLogicProof
open InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Eliminate the two actual child-output existentials in their original
scopes, transporting all shared original constructor and guard graphs. -/
theorem applicationFromChildExistence (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (arrow d e fp ap fn arg parent : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma
      (graph1 (rootGuard (validity old member) member) (suc z) parent)))
    (hf : Nonempty (Derivation body Gamma (hasCertifiedOutput old R member fn arrow)))
    (ha : Nonempty (Derivation body Gamma (hasCertifiedOutput old R member arg d))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member parent e)) := by
  apply hasCertifiedOutputCases old R member fn arrow _ hf
  intro β j Delta functionOut hj hfn
  rw [hasCertifiedOutputRename]
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have ha' := renameInto ha j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  rw [hasCertifiedOutputRename] at ha'
  apply hasCertifiedOutputCases old R member (arg.relabel j) (d.relabel j) _ ha'
  intro γ k E argumentOut hk harg
  rw [hasCertifiedOutputRename]
  have hc'' := renameInto hc' k E hk
  have hg'' := renameInto hg' k E hk
  have hfn' := renameInto hfn k E hk
  simp only [conjunctionRename,graph2Rename,graph4Rename] at hc''
  simp only [graph1Rename,sucRelabel,zRelabel] at hg''
  rw [certifiedOutputRename] at hfn'
  exact applicationHasOutput old R member ((arrow.relabel j).relabel k)
    ((d.relabel j).relabel k) ((e.relabel j).relabel k) ((fp.relabel j).relabel k)
    ((ap.relabel j).relabel k) ((fn.relabel j).relabel k) ((arg.relabel j).relabel k)
    ((parent.relabel j).relabel k) (functionOut.relabel k) argumentOut hc'' hg'' hfn' harg

/-- Only original child payloads decrease. Both child certifications are
obtained by instantiating the actual internal smaller-payload hypothesis. -/
theorem openingHasOutput (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (p input typ payload middle children arrow d e fp ap fn arg : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload old R member p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises old member input typ)))
    (hw : Nonempty (Derivation body Gamma
      (openingWitnesses (validity old member) member input
        payload middle children arrow d e fp ap fn arg))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member input typ)) := by
  have hc := andLeft hw
  have hv := andLeft (andRight hw)
  have hfields := andLeft (andRight (andRight hw))
  have hsmall := andRight (andRight (andRight (andRight hw)))
  obtain ⟨hep⟩ := valueUnique InternalUnpair.right payload p (Fin.cons input Fin.elim0)
    (andLeft (andRight hfields)) hr
  obtain ⟨hfp⟩ := andLeft hsmall
  obtain ⟨hap⟩ := andRight hsmall
  have hf := belowPayloadApply old R member p fp fn arrow hb
    ⟨orderRight fp hep hfp⟩ (andLeft (andRight (andRight (andRight hfields))))
    (andIntro (andLeft (andRight hv)) (andLeft (andRight (andRight hfields))))
  have ha := belowPayloadApply old R member p ap arg d hb
    ⟨orderRight ap hep hap⟩ (andRight (andRight (andRight (andRight (andRight hfields)))))
    (andIntro (andLeft (andRight (andRight hv)))
      (andLeft (andRight (andRight (andRight (andRight hfields))))))
  have hopen := InternalCanonicalResultFoldOpeningQueryProof.acceptWitnesses
    (validity old member) member input payload middle children arrow d e fp ap fn arg hw
  have hg := andRight (conjunctionRecover _ _ (Fin.cons input Fin.elim0) hopen)
  have he := valueUnique InternalUnpair.left e typ (Fin.cons input Fin.elim0)
    (andLeft hfields) (andRight hs)
  exact hasOutputTagTransport old R member input e typ he
    (applicationFromChildExistence old R member arrow d e fp ap fn arg input hc hg hf ha)

/-- Opening is recovered from actual acceptance, not from supplied source
inversion, constructors, child success, decoded terms or payload bounds. -/
theorem acceptedHasOutput (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (p input typ : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload old R member p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises old member input typ)))
    (hg : Nonempty (Derivation body Gamma
      (openingAccepted (validity old member) member input))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member input typ)) := by
  apply openingCases (validity old member) member input _ hg
  intro β j Delta payload middle children arrow d e fp ap fn arg hj hw
  rw [hasCertifiedOutputRename]
  have hb' := renameInto hb j Delta hj
  have hr' := renameInto hr j Delta hj
  have hs' := renameInto hs j Delta hj
  rw [belowPayloadRename] at hb'
  rw [graph1Rename] at hr'
  rw [sourcePremisesRename] at hs'
  exact openingHasOutput old R member (p.relabel j) (input.relabel j) (typ.relabel j)
    payload middle children arrow d e fp ap fn arg hb' hr' hs' hw

/-- An internal excluded-middle split on exact-one opening acceptance. Its
rejecting side derives the zero graph by the original conjunction laws. -/
theorem stepAtInput (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (p input typ : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload old R member p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises old member input typ))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member input typ)) := by
  let accepted := openingAccepted (validity old member) member input
  obtain ⟨hb⟩ := hb
  obtain ⟨hr⟩ := hr
  obtain ⟨hs⟩ := hs
  obtain ⟨hy⟩ := acceptedHasOutput (body := body) (Gamma := accepted :: Gamma)
    old R member p input typ ⟨addHyp hb accepted⟩ ⟨addHyp hr accepted⟩ ⟨addHyp hs accepted⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz : Nonempty (Derivation body (accepted.not :: Gamma)
      (graph1 (InternalApplicationResultStack.openGuard
        (rootGuard (validity old member) member)) z input)) :=
    InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
      (Fin.cons input Fin.elim0) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := leafHasOutput (body := body) (Gamma := accepted.not :: Gamma)
    old R member input typ ⟨addHyp hs accepted.not⟩ hz
  exact ⟨disjunctionElimination (excludedMiddle accepted)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

/-- Bind every original packed input and requested type inside this payload
step. The smaller-payload hypothesis remains the only undischarged premise. -/
theorem payloadStep (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (p : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload old R member p))) :
    Nonempty (Derivation body Gamma (atPayload old R member p)) := by
  apply atPayloadIntro old R member p
  let input : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let typ : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let Delta := sourcePremises old member input typ ::
    graph1 InternalUnpair.right (p.relabel Sum.inl) input ::
      Gamma.map (fun q => q.relabel Sum.inl)
  have hb' := renameInto hb (Sum.inl : α → α ⊕ Fin 2) Delta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)))
  rw [belowPayloadRename] at hb'
  obtain ⟨h⟩ := stepAtInput old R member (p.relabel Sum.inl) input typ hb'
    (show Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (p.relabel Sum.inl) input)) from
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    (show Nonempty (Derivation body Delta (sourcePremises old member input typ)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

/-- Discharge the step by the checked strong-induction rule in the original
calculus. No structural recursion or external semantic invariant is assumed. -/
theorem actualOriginalCanonicalFoldPayloadInvariant :
    ActualOriginalCanonicalFoldPayloadInvariant := by
  intro body old R member α Gamma payload
  apply payloadInduction old R member payload
  intro β Delta p hb
  exact payloadStep old R member p hb

/-- The original right selector supplies its own payload witness internally. -/
theorem certifiedOutputExists (old : InternalOriginalStepGuard.Data) (R member : Program 1)
    (input typ : OTerm α)
    (hs : Nonempty (Derivation body Gamma (sourcePremises old member input typ))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old R member input typ)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro β j Delta payload hj hr
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hr
  have hs' := renameInto hs j Delta hj
  rw [sourcePremisesRename] at hs'
  exact atPayloadApply old R member payload (input.relabel j) (typ.relabel j)
    (actualOriginalCanonicalFoldPayloadInvariant body old R member β Delta payload) hr hs'

theorem actualOriginalCanonicalFoldCertifiedOutput :
    ActualOriginalCanonicalFoldCertifiedOutput := by
  intro body old R member α Gamma input typ
  obtain ⟨h⟩ := certifiedOutputExists (body := body)
    (Gamma := sourcePremises old member input typ :: Gamma) old R member input typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantInductionProof
