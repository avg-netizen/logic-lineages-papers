module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityConsumerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityClosure (applicationConstructors)
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalParameterizedCanonicalResultFoldOpeningProof InternalParameterizedCanonicalResultFoldConsumerProof
open OriginalCanonicalApplicationInversionTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Reverse the full application fold at actual internally supplied outputs.
Parent validity supplies child validity and membership; the final selected
representative remains an explicit graph at the rebuilt original application. -/
theorem atValues (data : Data)
    (arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg input)))
    (hv : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) input parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data out input parameter)))
    (hf : Nonempty (Derivation body Gamma (foldGraph data functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (foldGraph data argumentOut arg parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application rebuilt d e functionOut argumentOut))) :
    Nonempty (Derivation body Gamma
      (Recovered data arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter)) := by
  have hchildren := OriginalApplicationInverseValidityProof.sourceRecover
    data arrow d e fp ap fn arg input parameter hc hv
  have hm := andLeft hchildren
  have hvf := andLeft (andRight hchildren)
  have hva := andRight (andRight hchildren)
  have hg := rootGuardValue data arrow d e fp ap fn arg input parameter hc hv hvf hva hm
  have hcf := certifiedAt data functionOut fn arrow parameter hvf
    (pairLeft fn arrow fp (andLeft (andRight hc))) hf
  have hca := certifiedAt data argumentOut arg d parameter hva
    (pairLeft arg d ap (andLeft (andRight (andRight hc)))) ha
  have hcombine := InternalParameterizedApplicationResultFoldTotalityConsumerProof.applicationBackward
    (rootGuard data) (leaf data) (combine data)
    arrow d e fp ap fn arg input functionOut argumentOut out parameter hc hg hf ha hn
  have hleaf := combineRecover data d e functionOut argumentOut rebuilt out parameter hr hcombine
  have hvrebuilt := rawValidity data arrow d e functionOut argumentOut rebuilt parameter
    (andLeft hc) (andLeft (andRight (andRight hcf))) (andLeft (andRight (andRight hca)))
    hm (andLeft (andRight hcf)) (andLeft (andRight hca)) hr
  exact andIntro hc (andIntro hm (andIntro hcf (andIntro hca
    (andIntro hr (andIntro (andIntro hvrebuilt (rawLeft d e functionOut argumentOut rebuilt hr)) hleaf)))))

/-- Bind both actual child-fold outputs and their rebuilt application through
three original Program queries, retaining every original raw constructor. -/
theorem atConstructors (data : Data)
    (arrow d e fp ap fn arg input out parameter : OTerm α) (psi : Formula α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg input)))
    (hv : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) input parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data out input parameter)))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
      ∀ functionOut argumentOut rebuilt : OTerm β,
      Nonempty (Derivation body Delta
        (Recovered data (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j)
          (ap.relabel j) (fn.relabel j) (arg.relabel j) functionOut argumentOut rebuilt
          (input.relabel j) (out.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let functionFold : Program 5 := .composition (foldN data) ![.projection 2,.projection 4]
  let argumentFold : Program 5 := .composition (foldN data) ![.projection 3,.projection 4]
  let rebuild : Program 5 := .composition application ![.projection 0,.projection 1,functionFold,argumentFold]
  let qs : Fin 3 → Program 5 := ![functionFold,argumentFold,rebuild]
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fn (Fin.cons arg (Fin.cons parameter Fin.elim0))))
  apply queryCases qs xs psi
  intro β j ys Delta hj hq
  have hc' := renameInto hc j Delta hj
  have hv' := renameInto hv j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  rw [foldGraphRename] at hn'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 5 → OTerm β := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))))
  have hf := binaryRecover (foldN data) (.projection 2) (.projection 4)
    (ys 0) (fn.relabel j) (parameter.relabel j) xx (hq 0)
    (projectionValue 2 xx) (projectionValue 4 xx)
  have ha := binaryRecover (foldN data) (.projection 3) (.projection 4)
    (ys 1) (arg.relabel j) (parameter.relabel j) xx (hq 1)
    (projectionValue 3 xx) (projectionValue 4 xx)
  have hr : Nonempty (Derivation body Delta
      (graph4 application (ys 2) (d.relabel j) (e.relabel j) (ys 0) (ys 1))) := by
    apply compositionRecover application ![.projection 0,.projection 1,functionFold,argumentFold]
      (ys 2) xx (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0))))
      (hq 2)
    intro i
    exact Fin.cases (projectionValue 0 xx) (Fin.cases (projectionValue 1 xx)
      (Fin.cases (hq 0) (Fin.cases (hq 1) (fun k => Fin.elim0 k)))) i
  exact next β j Delta hj (ys 0) (ys 1) (ys 2)
    (atValues data (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
      (fn.relabel j) (arg.relabel j) (ys 0) (ys 1) (ys 2) (input.relabel j) (out.relabel j)
      (parameter.relabel j) hc' hv' hn' hf ha hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionProof
