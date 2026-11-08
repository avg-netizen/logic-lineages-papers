module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceCombineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationStepPeelSupportProof
open InternalApplicationCertificateConstructors InternalRepresentativeApplicationCongruence
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalRepresentativeApplicationCongruenceCombineProof InternalRepresentativeApplicationCongruenceSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Equal actual function payloads suffice for the unchanged combine; both
child success graphs and the original parent guard are retained. -/
theorem applicationAtPayload (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data)
    (arrow d e fp ap fn arg parent x out y payload : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (applicationPremises validity member old arrow d e fp ap fn arg parent x out)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (InternalRepresentativeFoldCalibration.normalizer validity member old) y fn)))
    (hx : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload x)))
    (hy : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload y))) :
    Nonempty (Derivation body Gamma
      (graph1 (goodRun validity member old) InternalOriginalStepGuard.one parent ⊓
        graph1 (InternalRepresentativeFoldCalibration.normalizer validity member old) out parent)) := by
  have hc := andLeft h
  have hv := andRight h
  have hhf := andLeft (andRight hv)
  have hha := andLeft (andRight (andRight hv))
  have hna := andLeft (andRight (andRight (andRight hv)))
  have htail := andRight (andRight (andRight (andRight hv)))
  have hparent := andLeft htail
  have hcombine := andRight htail
  have harg := andLeft (andRight (andRight hc))
  have hcombine' := combinePayloadExtensionality old d e x y arg payload ap out hx hy
    (pairRight arg d ap harg) hcombine
  exact InternalApplicationCertifiedResultFoldClosureApplicationProof.applicationClosure
    (InternalRepresentativeFoldCalibration.rootGuard validity member)
    (InternalRepresentativeFoldCalibration.leaf validity member old)
    (InternalRepresentativeFoldCalibration.combine old)
    arrow d e fp ap fn arg parent y arg out
    (andLeft hc) (andLeft (andRight hc)) harg (andRight (andRight (andRight hc)))
    hparent (andIntro hhf hn) (andIntro hha hna) hcombine'

/-- A totality witness for the right payload is scoped and eliminated
internally. The old output y need not equal the wrapped output x. -/
theorem applicationAtOutput (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data) (valid p : Program 1)
    (arrow d e fp ap fn arg parent x out y : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (applicationPremises validity member old arrow d e fp ap fn arg parent x out)))
    (hr : Nonempty (Derivation body Gamma
      (InternalRepresentativeTag.representation valid p x fn)))
    (hp : Nonempty (Derivation body Gamma (graph1 p y fn)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (InternalRepresentativeFoldCalibration.normalizer validity member old) y fn))) :
    Nonempty (Derivation body Gamma
      (graph1 (goodRun validity member old) InternalOriginalStepGuard.one parent ⊓
        graph1 (InternalRepresentativeFoldCalibration.normalizer validity member old) out parent)) := by
  apply programCases InternalUnpair.right (Fin.cons x Fin.elim0) _
  intro β j Delta payload hj hx
  simp only [conjunctionRename,graph1Rename,oneRename]
  simp only [consTermRename,emptyRename] at hx
  have h' := renameInto h j Delta hj
  have hr' := renameInto hr j Delta hj
  have hp' := renameInto hp j Delta hj
  have hn' := renameInto hn j Delta hj
  simp only [applicationPremisesRename,representationRename,graph1Rename] at h' hr' hp' hn'
  exact applicationAtPayload validity member old (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (parent.relabel j)
    (x.relabel j) (out.relabel j) (y.relabel j) payload h' hn' hx
    (payloadAtOutput valid p payload (x.relabel j) (fn.relabel j) (y.relabel j) hr' hp' hx)

theorem sourceApplication (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data)
    (arrow d e fp ap fn arg parent x out : OTerm α)
    (hr : Nonempty (Derivation body Gamma
      (graph1 (data validity member old).sourceRepresentative x fn)))
    (h : Nonempty (Derivation body Gamma
      (applicationPremises validity member old arrow d e fp ap fn arg parent x out))) :
    Nonempty (Derivation body Gamma
      (graph1 (goodRun validity member old) InternalOriginalStepGuard.one parent ⊓
        graph1 (data validity member old).sourceRepresentative out parent)) := by
  apply programCases (InternalRepresentativeFoldCalibration.normalizer validity member old)
    (Fin.cons fn Fin.elim0) _
  intro β j Delta y hj hn
  simp only [conjunctionRename,graph1Rename,oneRename]
  simp only [consTermRename,emptyRename] at hn
  have hr' := renameInto hr j Delta hj
  have h' := renameInto h j Delta hj
  simp only [graph1Rename,applicationPremisesRename] at hr' h'
  have hv := andLeft (andRight h')
  have hp := foldedSourceAtNormalizer validity member old y (fn.relabel j) hv hn
  have hfold := applicationAtOutput validity member old
    (InternalApplicationValidityStack.recursiveData validity member).sourceValid
    (InternalRepresentativeFoldCalibration.foldedData validity member old).sourceRepresentative
    (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
    (fn.relabel j) (arg.relabel j) (parent.relabel j) (x.relabel j) (out.relabel j) y
    h' (andIntro hv hr') hp hn
  have hc := andLeft h'
  have htail := andRight (andRight (andRight (andRight (andRight h'))))
  have hvp := andLeft htail
  have hcombine := andRight htail
  have hparentTag := packedApplicationTag (d.relabel j) (e.relabel j) (fp.relabel j)
    (ap.relabel j) (parent.relabel j) (andRight (andRight (andRight hc)))
  have houtTag := combineTag old (d.relabel j) (e.relabel j) (x.relabel j)
    (arg.relabel j) (out.relabel j) hcombine
  have hwrapped := representativeAtOutput
    (InternalApplicationValidityStack.recursiveData validity member).sourceValid
    (InternalRepresentativeFoldCalibration.foldedData validity member old).sourceRepresentative
    (e.relabel j) (out.relabel j) (parent.relabel j) hvp
    (foldedSourceAtNormalizer validity member old (out.relabel j) (parent.relabel j)
      hvp (andRight hfold)) hparentTag houtTag
  exact andIntro (andLeft hfold) hwrapped

theorem targetApplication (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data)
    (arrow d e fp ap fn arg parent x out : OTerm α)
    (hr : Nonempty (Derivation body Gamma
      (graph1 (data validity member old).targetRepresentative x fn)))
    (h : Nonempty (Derivation body Gamma
      (applicationPremises validity member old arrow d e fp ap fn arg parent x out))) :
    Nonempty (Derivation body Gamma
      (graph1 (goodRun validity member old) InternalOriginalStepGuard.one parent ⊓
        graph1 (data validity member old).targetRepresentative out parent)) := by
  apply programCases (InternalRepresentativeFoldCalibration.normalizer validity member old)
    (Fin.cons fn Fin.elim0) _
  intro β j Delta y hj hn
  simp only [conjunctionRename,graph1Rename,oneRename]
  simp only [consTermRename,emptyRename] at hn
  have hr' := renameInto hr j Delta hj
  have h' := renameInto h j Delta hj
  simp only [graph1Rename,applicationPremisesRename] at hr' h'
  have hv := sourceToTarget validity member (fn.relabel j) (andLeft (andRight h'))
  have hfold := applicationAtOutput validity member old
    (InternalApplicationValidityStack.recursiveData validity member).targetValid
    (InternalRepresentativeFoldCalibration.normalizer validity member old)
    (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
    (fn.relabel j) (arg.relabel j) (parent.relabel j) (x.relabel j) (out.relabel j) y
    h' (andIntro hv hr') hn hn
  have hc := andLeft h'
  have htail := andRight (andRight (andRight (andRight (andRight h'))))
  have hvp := sourceToTarget validity member (parent.relabel j) (andLeft htail)
  have hcombine := andRight htail
  have hparentTag := packedApplicationTag (d.relabel j) (e.relabel j) (fp.relabel j)
    (ap.relabel j) (parent.relabel j) (andRight (andRight (andRight hc)))
  have houtTag := combineTag old (d.relabel j) (e.relabel j) (x.relabel j)
    (arg.relabel j) (out.relabel j) hcombine
  have hwrapped := representativeAtOutput
    (InternalApplicationValidityStack.recursiveData validity member).targetValid
    (InternalRepresentativeFoldCalibration.normalizer validity member old)
    (e.relabel j) (out.relabel j) (parent.relabel j) hvp (andRight hfold) hparentTag houtTag
  exact andIntro (andLeft hfold) hwrapped

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceApplicationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceApplicationProof
