module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaTypedLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaProperExitProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc z)
open NumberedWindowInternalSparseRawLambdaFrame (endpointTerm witnessTerm)
open NumberedWindowInternalSparseRawLambdaRun (lambdaFallback)
open NumberedWindowInternalSparseRawLambdaTypedLiftProof (exact_OpenTypedRaw5LambdaLift)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftInputs liftedEndpointGuards liftedSingletonFacts)
open NumberedWindowInternalSparseTypedRawLiftChecks (exact_OpenInstalledTypedRaw5LiftedSingleton)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)

attribute [local irreducible] programGraph

/-- From a genuine body step under the pushed lexical context, take
original tag1 under the abstraction, then original tag5 under the
auxiliary function. The original argument is the same raw term in
both tapes. Reinstall the actual positive one-hop certificate in the
same selected ID1 body and export its genuine even edge. -/
theorem exact_OpenLiteralLambdaProperExit
    (i j cv tv : Program 1) (d root other W least : Program 3) (V : Program 1)
    (n : Nat) (α : Type) (Γ : List (Formula α))
    (left right ctx dom cod fromClass toClass arg fromBody child toBody : OTerm α) :
    let Q := lambdaFallback other
    let raw := typedRaw5 root Q W V
    let R := addressPositive cv tv raw least
    let S := data i j R d
    let B := sourceBody S n
    let fromFn := endpointTerm dom fromBody
    let toFn := endpointTerm dom toBody
    let x := auxiliaryTerm dom cod fromFn arg
    let y := auxiliaryTerm dom cod toFn arg
    let w := functionWitnessTerm (witnessTerm child)
    let cert := singletonCertificate toClass x w y
    Nonempty (Derivation B Γ (programGraph raw (suc z)
      ![rawCons dom ctx,cod,fromBody,child,toBody])) →
    Nonempty (Derivation B Γ (liftedEndpointGuards W V ctx (rawCons dom cod) fromFn toFn)) →
    Nonempty (Derivation B Γ (liftedEndpointGuards W V ctx cod x y)) →
    Nonempty (Derivation B Γ (liftedSingletonFacts cv tv least left right ctx cod fromClass toClass x y)) →
    Nonempty (Derivation B Γ (certificate S false n left right cert ⊓ edge S false n left right)) := by
  intro Q raw R S B fromFn toFn x y w cert step fnGuards auxGuards facts
  obtain ⟨first⟩ := exact_OpenTypedRaw5LambdaLift root other W V ctx dom cod fromBody child toBody step fnGuards
  obtain ⟨second⟩ := auxGuards
  obtain ⟨physical⟩ := facts
  have inputs : Derivation B Γ
      (liftInputs root Q W V ctx dom cod arg fromFn (witnessTerm child) toFn) :=
    Derivation.conjunctionIntroduction first second
  obtain ⟨rule⟩ := exact_OpenInstalledTypedRaw5LiftedSingleton i j cv tv d root Q W least V n α Γ
    left right ctx dom cod fromClass toClass arg fromFn (witnessTerm child) toFn
  have installed :=
    Derivation.implicationElimination rule (Derivation.conjunctionIntroduction inputs physical)
  have certified : Nonempty (Derivation B Γ (certificate S false n left right cert)) :=
    (exact_CertificateRules i j R d false n B α Γ left right cert).2 ⟨installed⟩
  obtain ⟨reached⟩ := edgeIntroduction certified
  obtain ⟨checked⟩ := certified
  exact ⟨Derivation.conjunctionIntroduction checked reached⟩

#print axioms exact_OpenLiteralLambdaProperExit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaProperExitProof
