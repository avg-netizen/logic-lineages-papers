module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalFixednessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalParameterizedCanonicalResultFold (foldGraph)
open OriginalFinalVariableCanonical OriginalFinalVariableCanonicalSupportProof
open OriginalFinalVariableWeakeningSupportProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem finalVariableEquation (guard : Program 1) (p : GlobalSourcePackage.Inputs)
    (out raw variableCode typ index parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (originalSourceValidity guard p) (numeral 1) raw parameter)))
    (hw : Nonempty (Derivation body Gamma (originalWindowGraph p raw parameter))) :
    Nonempty (Derivation body Gamma
      ((foldGraph (OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p))
        out raw parameter).iff (equal out raw))) := by
  let q := OriginalVariableLeaves.refineInputs guard p
  have hD := finalVariableSelectedData q
  have hv' : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalVariableRepresentative.selectedData (finalVariableBase q) q.window))
        (numeral 1) raw parameter)) := by
    rw [← hD]
    exact hv
  have h := variableEquation (finalVariableBase q) q.window out raw variableCode typ index parameter hc hp hv' hw
  rw [← hD] at h
  exact h

/-- Both actual parameter pairs have the same outer Context. The original
window therefore transports internally without any Gamma membership premise. -/
theorem shiftedWindow (p : GlobalSourcePackage.Inputs)
    (raw shifted parameter extendedParameter context gamma extendedGamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma)))
    (he : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing extendedParameter context extendedGamma)))
    (hw : Nonempty (Derivation body Gamma (originalWindowGraph p raw parameter))) :
    Nonempty (Derivation body Gamma (originalWindowGraph p shifted extendedParameter)) :=
  iffBackward (contextCheckEquation p.window (numeral 1) shifted extendedParameter context extendedGamma he)
    (iffForward (contextCheckEquation p.window (numeral 1) raw parameter context gamma hp) hw)

/-- Exact all-output fixedness at the original and successor payloads. The
shifted source acceptance is paid by the preceding all-output weakening law. -/
theorem actualOriginalFinalVariableFixedness :
    OriginalFinalVariableCanonicalTargets.ActualOriginalFinalVariableFixedness := by
  intro guard p body alpha Delta out shiftedOut raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  let A := OriginalFinalVariableWeakening.Shape raw shifted variableCode shiftedVariable typ index
      parameter extendedParameter context gamma extendedGamma addedType ⊓
    (graph2 (originalSourceValidity guard p) (numeral 1) raw parameter ⊓
      originalWindowGraph p raw parameter)
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := andLeft ha
  have hv := andLeft (andRight ha)
  have hw := andRight (andRight ha)
  have hc := andLeft hs
  have hcs := andLeft (andRight hs)
  have hp := andLeft (andRight (andRight hs))
  have hps := andLeft (andRight (andRight (andRight hs)))
  have hparam := andLeft (andRight (andRight (andRight (andRight hs))))
  have heparam := andRight (andRight (andRight (andRight (andRight (andRight hs)))))
  have hws := shiftedWindow p raw shifted parameter extendedParameter context gamma extendedGamma
    hparam heparam hw
  obtain ⟨hweak⟩ := OriginalFinalVariableWeakeningProof.actualOriginalFinalVariableSourceWeakening
    guard p body alpha (A :: Delta) (numeral 1) raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  obtain ⟨hs'⟩ := hs
  have hvs := iffForward ⟨Derivation.implicationElimination hweak hs'⟩ hv
  obtain ⟨hr⟩ := andIntro
    (finalVariableEquation guard p out raw variableCode typ index parameter hc hp hv hw)
    (finalVariableEquation guard p shiftedOut shifted shiftedVariable typ (OrdinaryArithmetic.succTerm index)
      extendedParameter hcs hps hvs hws)
  exact ⟨Derivation.implicationIntroduction hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalFixednessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalFixednessProof
