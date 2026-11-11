module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaTraversalInternal OriginalLambdaTraversalSelection
open OriginalLambdaTraversalSelectionFieldProof OriginalLambdaTraversalSelectionValidityProof
open OriginalLambdaTraversalLambdaSourceProof OriginalLambdaTraversalLambdaRootProof
open OriginalLambdaTraversalLambdaStateProof OriginalLambdaTraversalLambdaSelectorProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Source premises transport by the three accepted literal field identities,
not by native evaluation or an identification of the two distinct Data. -/
theorem finalSourcePremises (p : GlobalSourcePackage.Inputs)
    (input typ parameter : OTerm alpha) :
    InternalParameterizedCanonicalResultFold.sourcePremises (finalData p) input typ parameter =
      InternalParameterizedCanonicalResultFold.sourcePremises (leafData p.base p.window) input typ parameter := by
  simp only [InternalParameterizedCanonicalResultFold.sourcePremises,
    InternalParameterizedCanonicalResultFold.validity, sameValidity]

/-- The actual final validator independently accepts the actual single
extended-Gamma child. Parent fixedness is not needed for this source fact. -/
theorem finalSourceChild (p : GlobalSourcePackage.Inputs)
    (input d e child parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields input d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter))) :
    Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one child bodyParameter ⊓ graph1 InternalUnpair.left e child)) := by
  have he := andLeft (andRight (andRight hf))
  have hb := andLeft (andRight (andRight (andRight hf)))
  have hp := andRight (andRight (andRight (andRight hf)))
  have hsource := sourceAccepted (finalData p) (finalInternalLaws p).2.1
    input parameter (andLeft hf) hs
  exact andIntro
    (finalChildAtSelectors _ input e child parameter bodyParameter he hb hp (andRight hsource))
    (bodyType input e child he hb)

/-- Child window and source/type use the SAME actual final tuple. -/
theorem finalChildPremises (p : GlobalSourcePackage.Inputs)
    (input d e child parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields input d e child parameter bodyParameter)))
    (hw : Nonempty (Derivation positive Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window input parameter)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter))) :
    Nonempty (Derivation positive Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p).window child bodyParameter ⊓
        InternalParameterizedCanonicalResultFold.sourcePremises (finalData p) child e bodyParameter)) :=
  andIntro
    (OriginalLambdaTraversalLambdaWindowProof.windowChild (finalInputs p).window InternalOriginalStepGuard.one
      input child parameter bodyParameter (andRight (andRight (andRight (andRight hf)))) hw)
    (finalSourceChild p input d e child parameter bodyParameter hf hs)

/-- Same-source transport is used only for the original constructor algebra;
this statement makes no claim that leafData is the final Data. -/
theorem finalSourceConstructor (p : GlobalSourcePackage.Inputs)
    (input d e child typ parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields input d e child parameter bodyParameter)))
    (ht : Nonempty (Derivation positive Delta (graph1 InternalUnpair.left typ input)))
    (hs : Nonempty (Derivation positive Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p))
        InternalOriginalStepGuard.one input parameter))) :
    Nonempty (Derivation positive Delta
      (graph2 OriginalLambdaConstructor.arrow typ d e ⊓
        graph3 OriginalLambdaConstructor.constructor input d e child)) := by
  rw [sameValidity] at hs
  exact sourceConstructor p.base p.window input d e child typ parameter bodyParameter hf ht hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalSourceProof
