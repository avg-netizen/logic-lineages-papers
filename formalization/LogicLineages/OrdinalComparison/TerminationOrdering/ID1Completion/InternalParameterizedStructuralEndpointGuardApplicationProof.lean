module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalParameterizedStructuralEndpointGuard
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalParameterizedApplicationValidityFold
open InternalApplicationValidityClosure (applicationConstructors)
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedStructuralEndpointGuardSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Packed target validation closes under the original application
constructor at the same parameter, with the original constant-one node. -/
theorem targetApplicationClosure (data : Data)
    (arrow d e fp ap fn arg parent parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hf : Nonempty (Derivation body Gamma (graph2 (targetValidity data) (suc z) fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 (targetValidity data) (suc z) arg parameter))) :
    Nonempty (Derivation body Gamma (graph2 (targetValidity data) (suc z) parent parameter)) := by
  obtain ⟨ht⟩ :=
    InternalParameterizedApplicationValidityFoldInternalProof.actualOriginalParameterizedValidityFoldApplicationClosure
      body (InternalLessThan.constantOne 2) data.oldTarget α Gamma
      arrow d e fp ap fn arg parent parameter
  obtain ⟨h⟩ := andIntro hc
    (andIntro (InternalLessThanSupportProof.oneConstantValue
      (Fin.cons e (Fin.cons parameter Fin.elim0))) (andIntro hf ha))
  exact ⟨Derivation.implicationElimination ht h⟩

/-- Original totality exposes both raw payloads, and the packed validator's
actual application clause closes the original parent graph. -/
theorem rawTargetValidity (data : Data) (arrow d e f a parent parameter : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hf : Nonempty (Derivation body Gamma (graph2 (targetValidity data) (suc z) f parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 (targetValidity data) (suc z) a parameter)))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a))) :
    Nonempty (Derivation body Gamma (graph2 (targetValidity data) (suc z) parent parameter)) := by
  let qs : Fin 2 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1)]
  let xs : Fin 2 → OTerm α := Fin.cons f (Fin.cons a Fin.elim0)
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  simp only [graph2Rename,sucRelabel,zRelabel]
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel] at har' hfl' hal' hf' ha' hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm β := Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)
  have hfr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (f.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have haright := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (a.relabel j)
    xx (hq 1) (projectionValue 1 xx)
  have hc := andIntro har'
    (andIntro (reconstructPair (f.relabel j) (arrow.relabel j) (ys 0) hfl' hfr)
      (andIntro (reconstructPair (a.relabel j) (d.relabel j) (ys 1) hal' haright)
        (applicationForward (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j)
          (ys 0) (ys 1) (parent.relabel j) hfr haright hp')))
  exact targetApplicationClosure data
    (arrow.relabel j) (d.relabel j) (e.relabel j) (ys 0) (ys 1)
    (f.relabel j) (a.relabel j) (parent.relabel j) (parameter.relabel j) hc hf' ha'

theorem applicationValue (data : Data)
    (arrow d e s t a sourceApp targetApp parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (applicationPremises data arrow d e s t a sourceApp targetApp parameter))) :
    Nonempty (Derivation body Gamma (applicationValidity data sourceApp targetApp e parameter)) := by
  have har := andLeft hp
  have hrest := andRight hp
  have hend := endpointRecover (validity data) (targetValidity data) data.member
    arrow d e s t a parameter har (andLeft hrest)
  have hs := andLeft hend
  have ht := andLeft (andRight hend)
  have ha := andLeft (andRight (andRight hend))
  have htail := andRight (andRight (andRight hend))
  have htags := andLeft htail
  have hm := andRight htail
  have hsapp := andLeft (andRight hrest)
  have htapp := andRight (andRight hrest)
  have hsparent := InternalParameterizedCanonicalResultFoldOpeningProof.rawValidity data
    arrow d e s a sourceApp parameter har (andLeft htags)
    (andRight (andRight htags)) hm hs ha hsapp
  have haTarget := andLeft (conjunctionRecover (targetP data.oldTarget)
    (universeP data.oldSource data.member) (Fin.cons a (Fin.cons parameter Fin.elim0)) ha)
  have htparent := rawTargetValidity data arrow d e t a targetApp parameter har
    (andLeft (andRight htags)) (andRight (andRight htags)) ht haTarget htapp
  exact andIntro hsparent (andIntro htparent
    (andIntro (InternalParameterizedCanonicalResultFoldOpeningProof.rawLeft d e s a sourceApp hsapp)
      (InternalParameterizedCanonicalResultFoldOpeningProof.rawLeft d e t a targetApp htapp)))

theorem actualParameterizedEndpointApplicationValidity :
    InternalParameterizedStructuralEndpointGuardTargets.ActualParameterizedEndpointApplicationValidity := by
  intro body data α Delta arrow d e s t a sourceApp targetApp parameter
  let P := applicationPremises data arrow d e s t a sourceApp targetApp parameter
  obtain ⟨h⟩ := applicationValue (body := body) (Gamma := P :: Delta)
    data arrow d e s t a sourceApp targetApp parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardApplicationProof
