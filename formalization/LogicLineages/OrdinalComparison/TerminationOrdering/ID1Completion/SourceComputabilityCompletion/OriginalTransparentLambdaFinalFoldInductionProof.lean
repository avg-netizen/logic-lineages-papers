module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldLaws
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentLambdaFinalFold OriginalTransparentLambdaFinalFoldLaws
open OriginalTransparentLambdaFinalFoldSyntaxProof OriginalTransparentLambdaFinalFoldBindingProof
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
variable (guard leaf valid : Program 2) (combine : Program 5)
variable (hleaf : LeafLaw body guard leaf valid)
variable (happ : ApplicationLaw body guard valid combine)
include hleaf happ

/-- The actual arbitrary leaf Program supplies its output inside the calculus. -/
theorem leafHasOutput (input parameter : OTerm α)
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z input parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf valid combine input parameter)) := by
  apply programCases leaf (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta out hj hl
  rw [hasCertifiedOutputRename]
  have hg' := renameInto hg j Delta hj
  simp only [graph2Rename,zRelabel] at hg'
  simp only [consTermRename,emptyRename] at hl
  apply hasCertifiedOutputIntro guard leaf valid combine out (input.relabel j) (parameter.relabel j)
  exact andIntro
    (InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
      guard leaf combine (input.relabel j) out (parameter.relabel j) hg' hl)
    (hleaf β Delta out (input.relabel j) (parameter.relabel j) hg' hl)

/-- The actual arbitrary quinary callback supplies its output after both
certified children. Function comes before argument and the parameter is shared. -/
theorem applicationFromOutputs (arrow d e fp ap fn arg parent functionOut argumentOut parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (commonFoldP guard leaf valid combine functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (commonFoldP guard leaf valid combine argumentOut arg parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf valid combine parent parameter)) := by
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
  rw [commonFoldPRename] at hf' ha'
  simp only [consTermRename,emptyRename] at hcomb
  apply hasCertifiedOutputIntro guard leaf valid combine out (parent.relabel j) (parameter.relabel j)
  exact andIntro
    (InternalParameterizedApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
      guard leaf combine (parameter.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
      (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
      (functionOut.relabel j) (argumentOut.relabel j) out
      (andLeft hc') (andLeft (andRight hc')) (andLeft (andRight (andRight hc')))
      (andRight (andRight (andRight hc'))) hg' (andLeft hf') (andLeft ha') hcomb)
    (happ β Delta (arrow.relabel j) (d.relabel j) (e.relabel j)
      (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
      (functionOut.relabel j) (argumentOut.relabel j) out (parameter.relabel j)
      hc' hg' (andRight hf') (andRight ha') hcomb)

/-- Both child witnesses are eliminated in their actual fresh-variable scopes. -/
theorem applicationFromChildExistence (arrow d e fp ap fn arg parent parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hf : Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf valid combine fn parameter)))
    (ha : Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf valid combine arg parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf valid combine parent parameter)) := by
  apply hasCertifiedOutputCases guard leaf valid combine fn parameter _ hf
  intro β j Delta functionOut hj hfn
  rw [hasCertifiedOutputRename]
  have hc' := renameInto hc j Delta hj
  have hg' := renameInto hg j Delta hj
  have ha' := renameInto ha j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  rw [hasCertifiedOutputRename] at ha'
  apply hasCertifiedOutputCases guard leaf valid combine (arg.relabel j) (parameter.relabel j) _ ha'
  intro γ k E argumentOut hk harg
  rw [hasCertifiedOutputRename]
  have hc'' := renameInto hc' k E hk
  have hg'' := renameInto hg' k E hk
  have hfn' := renameInto hfn k E hk
  simp only [conjunctionRename,graph2Rename,graph4Rename] at hc''
  simp only [graph2Rename,sucRelabel,zRelabel] at hg''
  rw [commonFoldPRename] at hfn'
  exact applicationFromOutputs guard leaf valid combine hleaf happ ((arrow.relabel j).relabel k)
    ((d.relabel j).relabel k) ((e.relabel j).relabel k) ((fp.relabel j).relabel k)
    ((ap.relabel j).relabel k) ((fn.relabel j).relabel k) ((arg.relabel j).relabel k)
    ((parent.relabel j).relabel k) (functionOut.relabel k) argumentOut
    ((parameter.relabel j).relabel k) hc'' hg'' hfn' harg

/-- Actual opening acceptance reconstructs both original children, whose
payloads strictly decrease. No source validity or type membership is needed. -/
theorem acceptedHasOutput (p input parameter : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload guard leaf valid combine p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf valid combine input parameter)) := by
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
  have hf := belowPayloadApply guard leaf valid combine (p.relabel j) fp fn (parameter.relabel j)
    hb' ⟨orderRight fp hep hfp⟩ hfn
  have ha := belowPayloadApply guard leaf valid combine (p.relabel j) ap arg (parameter.relabel j)
    hb' ⟨orderRight ap hep hap⟩ harg
  exact applicationFromChildExistence guard leaf valid combine hleaf happ arrow d e fp ap fn arg
    (input.relabel j) (parameter.relabel j) hc hguard hf ha

/-- The existing normalized conjunction splits at exact ONE; rejection gives
its actual ZERO graph even when the arbitrary callback G is not Boolean. -/
theorem stepAtInput (p input parameter : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload guard leaf valid combine p)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right p input))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf valid combine input parameter)) := by
  let accepted := graph2 (InternalParameterizedApplicationResultStack.openGuardP guard)
    (suc z) input parameter
  obtain ⟨hb⟩ := hb
  obtain ⟨hr⟩ := hr
  obtain ⟨hy⟩ := acceptedHasOutput (body := body) (Gamma := accepted :: Gamma)
    guard leaf valid combine hleaf happ p input parameter ⟨addHyp hb accepted⟩ ⟨addHyp hr accepted⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz : Nonempty (Derivation body (accepted.not :: Gamma)
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z input parameter)) :=
    InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
      (Fin.cons input (Fin.cons parameter Fin.elim0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := leafHasOutput (body := body) (Gamma := accepted.not :: Gamma)
    guard leaf valid combine hleaf happ input parameter hz
  exact ⟨disjunctionElimination (excludedMiddle accepted)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

/-- Bind every original packed input and parameter inside the payload step. -/
theorem payloadStep (p : OTerm α)
    (hb : Nonempty (Derivation body Gamma (belowPayload guard leaf valid combine p))) :
    Nonempty (Derivation body Gamma (atPayloadP guard leaf valid combine p)) := by
  apply atPayloadIntro guard leaf valid combine p
  let input : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let parameter : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let Delta := graph1 InternalUnpair.right (p.relabel Sum.inl) input ::
    Gamma.map (fun q => q.relabel Sum.inl)
  have hb' := renameInto hb (Sum.inl : α → α ⊕ Fin 2) Delta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowPayloadRename] at hb'
  obtain ⟨h⟩ := stepAtInput guard leaf valid combine hleaf happ (p.relabel Sum.inl) input parameter hb'
    (show Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (p.relabel Sum.inl) input)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Genuine strong induction on the original payload proves a common output
for every input and parameter, including zero and malformed inputs. -/
theorem payloadCommonOutput (payload : OTerm α) :
    Nonempty (Derivation body Gamma (atPayloadP guard leaf valid combine payload)) := by
  apply payloadInduction guard leaf valid combine payload
  intro β Delta p hb
  exact payloadStep guard leaf valid combine hleaf happ p hb

/-- Obtain the original input payload internally and instantiate the invariant. -/
theorem commonOutputExists (input parameter : OTerm α) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf valid combine input parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro β j Delta payload hj hr
  rw [hasCertifiedOutputRename]
  simp only [consTermRename,emptyRename] at hr
  exact atPayloadApply guard leaf valid combine payload (input.relabel j) (parameter.relabel j)
    (payloadCommonOutput guard leaf valid combine hleaf happ payload) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldInductionProof
