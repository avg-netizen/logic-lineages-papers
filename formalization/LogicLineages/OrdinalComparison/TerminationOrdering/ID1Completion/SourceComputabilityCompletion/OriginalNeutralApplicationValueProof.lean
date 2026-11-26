module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (binaryValue)
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof (symm)
open OriginalApplicationSidecar OriginalNeutralApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Reverse the existing actualJ composition using its actual argument fold.
The original function input is a projection throughout this composition. -/
theorem applicationFromCombine (data : Data)
    (d e function argument out parameter argumentOut : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph data argumentOut argument parameter)))
    (hc : Nonempty (Derivation body Gamma
      (programGraph (InternalParameterizedCanonicalResultFold.combine data) out
        (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argumentOut (Fin.cons parameter Fin.elim0)))))))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph data out d e function argument parameter)) := by
  let xs : Fin 5 → OTerm alpha :=
    Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.cons parameter Fin.elim0))))
  apply compositionValue (InternalParameterizedCanonicalResultFold.combine data)
    ![.projection 0,.projection 1,.projection 2,
      .composition (InternalParameterizedCanonicalResultFold.foldN data) ![.projection 3,.projection 4],.projection 4]
    out xs (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))) hc
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases
      (binaryValue (InternalParameterizedCanonicalResultFold.foldN data)
        (.projection 3) (.projection 4) argumentOut argument parameter xs hn
        (projectionValue 3 xs) (projectionValue 4 xs))
      (Fin.cases (projectionValue 4 xs) (fun q ↦ Fin.elim0 q))))) i

/-- The SAME leaf is the identity at the actual rebuilt application.
Program functionality transfers the original constructor to actualJ's output. -/
theorem forwardAtRaw (data : Data) (window : Program 1)
    (arrow d e function argument out argumentOut rebuilt parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma
      (InputPremises (selectedData data window) window arrow d e function argument parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window)
        argumentOut argument parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application rebuilt d e function argumentOut)))
    (hj : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph
        (selectedData data window) out d e function argument parameter))) :
    Nonempty (Derivation body Gamma (graph4 application out d e function argumentOut)) := by
  have hself := OriginalNeutralApplicationLeafProof.rawLeafValue
    data window arrow d e function argument argumentOut rebuilt parameter hp hn hr
  have hcombine := InternalOriginalUniformApplicationTypingApplicationProof.applicationCombine
    (selectedData data window) d e function argument out parameter argumentOut hn hj
  have hleaf := InternalParameterizedCanonicalResultFoldOpeningProof.combineRecover
    (selectedData data window) d e function argumentOut rebuilt out parameter hr hcombine
  obtain ⟨heq⟩ := valueUnique (InternalParameterizedCanonicalResultFold.leaf (selectedData data window))
    out rebuilt (Fin.cons rebuilt (Fin.cons parameter Fin.elim0)) hleaf hself
  exact outputTransport application rebuilt out
    (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argumentOut Fin.elim0)))) ⟨symm heq⟩ hr

theorem backward (data : Data) (window : Program 1)
    (arrow d e function argument out argumentOut parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma
      (InputPremises (selectedData data window) window arrow d e function argument parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window)
        argumentOut argument parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application out d e function argumentOut))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph
        (selectedData data window) out d e function argument parameter)) := by
  have hself := OriginalNeutralApplicationLeafProof.rawLeafValue
    data window arrow d e function argument argumentOut out parameter hp hn hr
  have hcombine := InternalParameterizedCanonicalResultFoldOpeningProof.combineValue
    (selectedData data window) d e function argumentOut out out parameter hr hself
  exact applicationFromCombine (selectedData data window)
    d e function argument out parameter argumentOut hn hcombine

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationValueProof
