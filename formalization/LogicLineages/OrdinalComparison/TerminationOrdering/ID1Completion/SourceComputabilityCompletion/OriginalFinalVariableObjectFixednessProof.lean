module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalFixednessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectFixednessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open InternalParameterizedCanonicalResultFold (foldGraph)
open OriginalFinalVariableCanonicalSupportProof (iffBackward)
open OriginalFinalVariableObject OriginalFinalVariableObjectWrapperSupportProof OriginalFinalVariableObjectInternalSupportProof
open OriginalRawObjectTransport UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Both payload self-graphs are derived at the SAME final tuple from only
the unchanged source/window premises. No canonical identity is assumed. -/
theorem variableFoldSelf (guard : Program 1) (p : GlobalSourcePackage.Inputs)
    (raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (OriginalFinalVariableWeakening.Shape raw shifted variableCode shiftedVariable typ index
          parameter extendedParameter context gamma extendedGamma addedType ⊓
        (graph2 (OriginalFinalVariableCanonical.originalSourceValidity guard p) (numeral 1) raw parameter ⊓
          OriginalFinalVariableCanonical.originalWindowGraph p raw parameter)))) :
    Nonempty (Derivation body Delta
      (foldGraph (OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p))
        raw raw parameter)) ∧
    Nonempty (Derivation body Delta
      (foldGraph (OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p))
        shifted shifted extendedParameter)) := by
  obtain ⟨hf⟩ := OriginalFinalVariableCanonicalFixednessProof.actualOriginalFinalVariableFixedness
    guard p body alpha Delta raw shifted raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  obtain ⟨ha'⟩ := ha
  have h := show Nonempty (Derivation body Delta _) from ⟨Derivation.implicationElimination hf ha'⟩
  exact ⟨iffBackward (andLeft h) (by simpa only [equalEqn] using
      (show Nonempty (Derivation body Delta (eqn raw raw)) from ⟨refl raw⟩)),
    iffBackward (andRight h) (by simpa only [equalEqn] using
      (show Nonempty (Derivation body Delta (eqn shifted shifted)) from ⟨refl shifted⟩))⟩

/-- Lift the source and successor variable rigidity through the ACTUAL Object
wrapper. Every genuine shift output is internally recovered from composition. -/
theorem actualOriginalFinalVariableObjectFixedness :
    OriginalFinalVariableObjectTargets.ActualOriginalFinalVariableObjectFixedness := by
  intro guard p body alpha Delta out shiftedOut input shiftedObject raw shifted variableCode shiftedVariable
    typ index parameter extendedParameter context gamma extendedGamma addedType
  let q := OriginalVariableLeaves.refineInputs guard p
  let A := Premise guard p input raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  let B := graph2 shiftObjectRaw shiftedObject addedType input
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hp := andLeft ha
  have hs := andLeft (andRight ha)
  have hparam := andLeft (andRight (andRight (andRight (andRight hs))))
  have hc := andLeft (andRight (andRight (andRight (andRight (andRight hs)))))
  have heparam := andRight (andRight (andRight (andRight (andRight (andRight hs)))))
  have hf := variableFoldSelf guard p raw shifted variableCode shiftedVariable typ index parameter extendedParameter
    context gamma extendedGamma addedType (andRight ha)
  have hself := wrapperBackward q context input input gamma raw parameter raw hp hparam hf.1 hp
  have hfirst := valueEquation (canonicalObjectProgram q) out input
    (Fin.cons context (Fin.cons input Fin.elim0)) hself
  have ht := OriginalFinalVariableCanonicalRawProof.packedVariableTransport
    raw shifted variableCode shiftedVariable typ index addedType
    (andLeft hs) (andLeft (andRight hs)) (andLeft (andRight (andRight hs)))
    (andLeft (andRight (andRight (andRight hs))))
  have hb : Nonempty (Derivation body (B :: A :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hpair := shiftObjectPair addedType input shiftedObject gamma raw extendedGamma shifted
    (addAssumption hp B) (addAssumption hc B) (addAssumption ht.1 B) hb
  have hshiftSelf := wrapperBackward q context shiftedObject shiftedObject extendedGamma shifted
    extendedParameter shifted hpair (addAssumption heparam B) (addAssumption hf.2 B) hpair
  obtain ⟨hsecond⟩ := valueEquation (canonicalObjectProgram q) shiftedOut shiftedObject
    (Fin.cons context (Fin.cons shiftedObject Fin.elim0)) hshiftSelf
  obtain ⟨hresult⟩ := andIntro hfirst
    (show Nonempty (Derivation body (A :: Delta) _) from ⟨Derivation.implicationIntroduction hsecond⟩)
  exact ⟨Derivation.implicationIntroduction hresult⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectFixednessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectFixednessProof
