module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformApplicationTyping InternalOriginalUniformApplicationTypingTargets
open InternalParameterizedCanonicalResultFold
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalParameterizedCanonicalResultFoldOpeningProof
open InternalParameterizedCanonicalResultFoldConsumerProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem typedGraphRename {β : Type} (data : Data)
    (value typ parameter : OTerm α) (j : α → β) :
    (typedGraph data value typ parameter).relabel j =
      typedGraph data (value.relabel j) (typ.relabel j) (parameter.relabel j) := by
  simp only [typedGraph,graph3Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem applicationPremisesRename {β : Type} (data : Data)
    (arrow d e f a out parameter : OTerm α) (j : α → β) :
    (applicationPremises data arrow d e f a out parameter).relabel j =
      applicationPremises data (arrow.relabel j) (d.relabel j) (e.relabel j)
        (f.relabel j) (a.relabel j) (out.relabel j) (parameter.relabel j) := by
  simp only [applicationPremises,conjunctionRename,graph2Rename,memberGraph,
    typedGraphRename,applicationGraphRename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

/-- Recover the actual combine at the internally supplied N(argument)
output. The function coordinate is the original supplied function itself. -/
theorem applicationCombine (data : Data) (d e f a out parameter b : OTerm α)
    (hn : Nonempty (Derivation body Gamma (foldGraph data b a parameter)))
    (hj : Nonempty (Derivation body Gamma (applicationGraph data out d e f a parameter))) :
    Nonempty (Derivation body Gamma
      (programGraph (combine data) out
        (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons b (Fin.cons parameter Fin.elim0))))))) := by
  let xs : Fin 5 → OTerm α :=
    Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a (Fin.cons parameter Fin.elim0))))
  apply compositionRecover (combine data)
    ![.projection 0,.projection 1,.projection 2,
      .composition (foldN data) ![.projection 3,.projection 4],.projection 4] out xs
    (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons b (Fin.cons parameter Fin.elim0))))) hj
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases
      (binaryValue (foldN data) (.projection 3) (.projection 4)
        b a parameter xs hn (projectionValue 3 xs) (projectionValue 4 xs))
      (Fin.cases (projectionValue 4 xs) (fun q => Fin.elim0 q))))) i

/-- Actual canonical-fold output invariants supply the normalized argument's
validity and original tag. Source application validity and descent then give
the supplied actualJ output its canonical typed graph, with no N-fixedness. -/
theorem applicationAtWitnesses (data : Data)
    (arrow d e f a out parameter b raw : OTerm α)
    (h : Nonempty (Derivation body Gamma (applicationPremises data arrow d e f a out parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data b a parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application raw d e f b))) :
    Nonempty (Derivation body Gamma (typedGraph data out e parameter)) := by
  have har := andLeft h
  have hm := andLeft (andRight h)
  have hf := andLeft (andRight (andRight h))
  have ha := andLeft (andRight (andRight (andRight h)))
  have hj := andRight (andRight (andRight (andRight h)))
  have hff := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (validity data) data.member f arrow parameter hf
  have haf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (validity data) data.member a d parameter ha
  have hb := andRight (certifiedAt data b a d parameter
    (andLeft (andRight haf)) (andLeft (andRight (andRight haf))) hn)
  have hv := rawValidity data arrow d e f b raw parameter har
    (andLeft (andRight (andRight hff))) (andLeft (andRight hb)) hm
    (andLeft (andRight hff)) (andLeft hb) hr
  have hd := combineRecover data d e f b raw out parameter hr
    (applicationCombine data d e f a out parameter b hn hj)
  have hi := InternalParameterizedCanonicalResultFoldLeafProof.descentInvariant
    data out raw e parameter hd (andIntro hv (rawLeft d e f b raw hr))
  exact InternalOriginalUniformDescentSelectionInternalProof.typedAccept
    data.oldRepresentative (validity data) data.member out e parameter (andIntro hm hi)

/-- The raw application's output is obtained internally from its original
Program graph and eliminated after proving the fixed supplied output's type. -/
theorem applicationAtArgument (data : Data)
    (arrow d e f a out parameter b : OTerm α)
    (h : Nonempty (Derivation body Gamma (applicationPremises data arrow d e f a out parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data b a parameter))) :
    Nonempty (Derivation body Gamma (typedGraph data out e parameter)) := by
  apply programCases application (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons b Fin.elim0)))) _
  intro β j Delta raw hj hr
  rw [typedGraphRename]
  have h' := renameInto h j Delta hj
  rw [applicationPremisesRename] at h'
  have hn' := renameInto hn j Delta hj
  rw [foldGraphRename] at hn'
  simp only [consTermRename,emptyRename] at hr
  exact applicationAtWitnesses data (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (out.relabel j) (parameter.relabel j) (b.relabel j) raw h' hn' hr

/-- N(argument) is an internal witness. Nothing identifies it with the
argument or introduces an N(function) graph. -/
theorem applicationTyped (data : Data) (arrow d e f a out parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (applicationPremises data arrow d e f a out parameter))) :
    Nonempty (Derivation body Gamma (typedGraph data out e parameter)) := by
  apply programCases (foldN data) (Fin.cons a (Fin.cons parameter Fin.elim0)) _
  intro β j Delta b hj hn
  rw [typedGraphRename]
  have h' := renameInto h j Delta hj
  rw [applicationPremisesRename] at h'
  simp only [consTermRename,emptyRename] at hn
  exact applicationAtArgument data (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (out.relabel j) (parameter.relabel j) b h' hn

theorem actualParameterizedCanonicalApplicationTypedOutput :
    ActualParameterizedCanonicalApplicationTypedOutput := by
  intro body data α Delta arrow d e f a out parameter
  let P := applicationPremises data arrow d e f a out parameter
  obtain ⟨h⟩ := applicationTyped (body := body) (Gamma := P :: Delta)
    data arrow d e f a out parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
