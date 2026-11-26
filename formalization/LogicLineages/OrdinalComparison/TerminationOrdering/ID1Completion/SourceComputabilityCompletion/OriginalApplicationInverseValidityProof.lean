module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalParameterizedApplicationValidityFold
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalApplicationValidityClosure (applicationConstructors)
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The actual parent output identifies both queried child outputs with one.
The combine equation is inverted internally, including its codomain test. -/
theorem recoverAtOutputs (node oldLeaf : Program 2)
    (arrow d e fp ap fn arg parent functionOut argumentOut parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hf : Nonempty (Derivation body Gamma
      (graph2 (validatorP node oldLeaf) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 (validatorP node oldLeaf) argumentOut arg parameter)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 (validatorP node oldLeaf) (suc z) parent parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 node (suc z) e parameter ⊓
        (graph2 (validatorP node oldLeaf) (suc z) fn parameter ⊓
          graph2 (validatorP node oldLeaf) (suc z) arg parameter))) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons functionOut
    (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))
  have hg : Nonempty (Derivation body Gamma (graph2 openingGuardP (suc z) parent parameter)) :=
    InternalLessThanSupportProof.oneConstantValue (Fin.cons parent (Fin.cons parameter Fin.elim0))
  have hcomb := InternalParameterizedApplicationResultFoldTotalityConsumerProof.applicationBackward
    openingGuardP (leafP oldLeaf) (combineP node) arrow d e fp ap fn arg parent
    functionOut argumentOut (suc z) parameter hc hg hf ha hp
  have hparts := conjunctionRecover (nodeAtP node)
    (InternalAcceptance.conjunction (.projection 2) (.projection 3)) xs hcomb
  have hchildren := conjunctionRecover (.projection 2) (.projection 3) xs (andRight hparts)
  have hfeq := valueUnique (.projection (2 : Fin 5)) functionOut (suc z) xs
    (projectionValue 2 xs) (andLeft hchildren)
  have haeq := valueUnique (.projection (3 : Fin 5)) argumentOut (suc z) xs
    (projectionValue 3 xs) (andRight hchildren)
  have hn := binaryRecover node (.projection 1) (.projection 4) (suc z) e parameter xs
    (andLeft hparts) (projectionValue 1 xs) (projectionValue 4 xs)
  exact andIntro hn
    (andIntro (outputTransport (validatorP node oldLeaf) functionOut (suc z)
      (Fin.cons fn (Fin.cons parameter Fin.elim0)) hfeq hf)
      (outputTransport (validatorP node oldLeaf) argumentOut (suc z)
        (Fin.cons arg (Fin.cons parameter Fin.elim0)) haeq ha))

/-- Child outputs are obtained by original Program totality and discharged by
existential elimination. No child-validity or successful-run premise occurs. -/
theorem applicationRecover (node oldLeaf : Program 2)
    (arrow d e fp ap fn arg parent parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 (validatorP node oldLeaf) (suc z) parent parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 node (suc z) e parameter ⊓
        (graph2 (validatorP node oldLeaf) (suc z) fn parameter ⊓
          graph2 (validatorP node oldLeaf) (suc z) arg parameter))) := by
  let qs : Fin 2 → Program 3 :=
    ![.composition (validatorP node oldLeaf) ![.projection 0,.projection 2],
      .composition (validatorP node oldLeaf) ![.projection 1,.projection 2] ]
  let xs : Fin 3 → OTerm α := Fin.cons fn (Fin.cons arg (Fin.cons parameter Fin.elim0))
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  simp only [conjunctionRename,graph2Rename,sucRelabel,zRelabel]
  have hc' := renameInto hc j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [graph2Rename,sucRelabel,zRelabel] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 3 → OTerm β := Fin.cons (fn.relabel j)
    (Fin.cons (arg.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
  have hf := binaryRecover (validatorP node oldLeaf) (.projection 0) (.projection 2)
    (ys 0) (fn.relabel j) (parameter.relabel j) xx (hq 0)
    (projectionValue 0 xx) (projectionValue 2 xx)
  have ha := binaryRecover (validatorP node oldLeaf) (.projection 1) (.projection 2)
    (ys 1) (arg.relabel j) (parameter.relabel j) xx (hq 1)
    (projectionValue 1 xx) (projectionValue 2 xx)
  exact recoverAtOutputs node oldLeaf (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (ys 0) (ys 1) (parameter.relabel j) hc' hf ha hp'

/-- Source validity is the actual conjunction of packed validity and universe
validity. Inverting both folds reconstructs that same conjunction at each child. -/
theorem sourceRecover (data : Data)
    (arrow d e fp ap fn arg parent parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 (validity data) (suc z) parent parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 data.member (suc z) e parameter ⊓
        (graph2 (validity data) (suc z) fn parameter ⊓
          graph2 (validity data) (suc z) arg parameter))) := by
  have hparts := conjunctionRecover (targetP data.oldTarget)
    (universeP data.oldSource data.member) (Fin.cons parent (Fin.cons parameter Fin.elim0)) hp
  have ht := applicationRecover (InternalLessThan.constantOne 2) data.oldTarget
    arrow d e fp ap fn arg parent parameter hc (andLeft hparts)
  have hu := applicationRecover data.member data.oldSource
    arrow d e fp ap fn arg parent parameter hc (andRight hparts)
  have hf := conjunctionAccept (targetP data.oldTarget) (universeP data.oldSource data.member)
    (Fin.cons fn (Fin.cons parameter Fin.elim0))
    (andLeft (andRight ht)) (andLeft (andRight hu))
  have ha := conjunctionAccept (targetP data.oldTarget) (universeP data.oldSource data.member)
    (Fin.cons arg (Fin.cons parameter Fin.elim0))
    (andRight (andRight ht)) (andRight (andRight hu))
  exact andIntro (andLeft hu) (andIntro hf ha)

/-- Restore the actual child payloads internally. The original raw type tags
prevent the payload-only application constructor from changing child types. -/
theorem rawSourceRecover (data : Data) (arrow d e fn arg parent parameter : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow fn)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d arg)))
    (happ : Nonempty (Derivation body Gamma (graph4 application parent d e fn arg)))
    (hp : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) parent parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 data.member (suc z) e parameter ⊓
        (graph2 (validity data) (suc z) fn parameter ⊓
          graph2 (validity data) (suc z) arg parameter))) := by
  let qs : Fin 2 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1)]
  let xs : Fin 2 → OTerm α := Fin.cons fn (Fin.cons arg Fin.elim0)
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  simp only [conjunctionRename,graph2Rename,sucRelabel,zRelabel]
  have har' := renameInto har j Delta hj
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have happ' := renameInto happ j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel] at har' hfl' hal' happ' hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm β := Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j) Fin.elim0)
  have hfr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (fn.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have haright := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (arg.relabel j)
    xx (hq 1) (projectionValue 1 xx)
  have hc := andIntro har'
    (andIntro (reconstructPair (fn.relabel j) (arrow.relabel j) (ys 0) hfl' hfr)
      (andIntro (reconstructPair (arg.relabel j) (d.relabel j) (ys 1) hal' haright)
        (applicationForward (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
          (ys 0) (ys 1) (parent.relabel j) hfr haright happ')))
  exact sourceRecover data (arrow.relabel j) (d.relabel j) (e.relabel j) (ys 0) (ys 1)
    (fn.relabel j) (arg.relabel j) (parent.relabel j) (parameter.relabel j) hc hp'

theorem actualValidatorApplicationInversion :
    OriginalApplicationInverseTargets.ActualValidatorApplicationInversion := by
  intro body node oldLeaf α Gamma arrow d e fp ap fn arg parent parameter
  let P := applicationConstructors arrow d e fp ap fn arg parent ⊓
    graph2 (validatorP node oldLeaf) (suc z) parent parameter
  have hp : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := applicationRecover node oldLeaf arrow d e fp ap fn arg parent parameter
    (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualSourceApplicationInversion :
    OriginalApplicationInverseTargets.ActualSourceApplicationInversion := by
  intro body data α Gamma arrow d e fn arg parent parameter
  let P := graph2 InternalListCodec.consCode arrow d e ⊓
    (graph1 InternalUnpair.left arrow fn ⊓
      (graph1 InternalUnpair.left d arg ⊓
        (graph4 application parent d e fn arg ⊓
          graph2 (validity data) (suc z) parent parameter)))
  have hp : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := rawSourceRecover data arrow d e fn arg parent parameter
    (andLeft hp) (andLeft (andRight hp)) (andLeft (andRight (andRight hp)))
    (andLeft (andRight (andRight (andRight hp)))) (andRight (andRight (andRight (andRight hp))))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
