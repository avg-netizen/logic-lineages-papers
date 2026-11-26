module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSelectorSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSelectorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalSelectorSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem projectionComposition (p : Program 1) (out raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (.composition p (fun _ : Fin 1 => .projection 0)) out raw parameter).iff
        (graph1 p out raw))) := by
  let xs : Fin 2 → OTerm alpha := ![raw,parameter]
  let A := graph2 (.composition p (fun _ : Fin 1 => .projection 0)) out raw parameter
  let B := graph1 p out raw
  obtain ⟨hf⟩ := unaryRecover p (.projection 0) out raw xs
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (projectionValue 0 xs)
  obtain ⟨hb⟩ := unaryValue p (.projection 0) out raw xs
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (projectionValue 0 xs)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem resultTypeValue (typ raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ raw))) :
    Nonempty (Derivation body Gamma (graph2 resultType typ raw parameter)) :=
  unaryValue InternalUnpair.left (.projection 0) typ raw ![raw,parameter] ht
    (projectionValue 0 ![raw,parameter])

theorem codomainRecover (out raw parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (graph2 codomain out raw parameter))) :
    Nonempty (Derivation body Gamma (CodomainGraph out raw)) := by
  apply queryCases (fun _ : Fin 1 => InternalUnpair.left) (Fin.cons raw Fin.elim0) _
  intro beta j ys Delta hj hq
  have hc' := renameInto hc j Delta hj
  simp only [graph2Rename] at hc'
  simp only [consTermRename,emptyRename] at hq
  simp only [codomainRename]
  exact codomainIntro (out.relabel j) (raw.relabel j) (ys 0)
    (andIntro (hq 0)
      (unaryRecover InternalListCodec.tailCode resultType (out.relabel j) (ys 0)
        ![raw.relabel j,parameter.relabel j] hc'
        (resultTypeValue (ys 0) (raw.relabel j) (parameter.relabel j) (hq 0))))

theorem codomainValue (out raw parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (CodomainGraph out raw))) :
    Nonempty (Derivation body Gamma (graph2 codomain out raw parameter)) := by
  apply codomainCases out raw _ hc
  intro beta j Delta typ hj hf
  simp only [graph2Rename]
  exact unaryValue InternalListCodec.tailCode resultType (out.relabel j) typ
    ![raw.relabel j,parameter.relabel j] (andRight hf)
    (resultTypeValue typ (raw.relabel j) (parameter.relabel j) (andLeft hf))

theorem codomainEquation (out raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 codomain out raw parameter).iff (CodomainGraph out raw))) := by
  let A := graph2 codomain out raw parameter
  let B := CodomainGraph out raw
  obtain ⟨hf⟩ := codomainRecover out raw parameter
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := codomainValue out raw parameter
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalTransparentInternalSelectors :
    OriginalTransparentLambdaValidityInternalTargets.ActualOriginalTransparentInternalSelectors := by
  intro body alpha out raw parameter
  exact ⟨projectionComposition InternalUnpair.left out raw parameter,
    projectionComposition OriginalLambdaConstructor.tag out raw parameter,
    projectionComposition OriginalLambdaConstructor.domain out raw parameter,
    codomainEquation out raw parameter⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSelectorProof
