module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTypeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (z zRelabel eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalUniverseDecoderInternalAcceptance
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem bottomPayload (H : Program 1) (M W : Program 2) (raw payload typ gamma c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw payload)))
    (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Delta (eqn payload typ)) := by
  have hf := iffForward (OriginalUniverseDecoderTransportLeafAcceptanceProof.bottomIff H M W raw payload typ gamma c hc) ha
  simpa only [equalEqn] using andRight hf

theorem lambdaFields (H : Program 1) (M W : Program 2)
    (raw domain child typ requested codomain gamma extended c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields typ requested codomain)))
    (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
    (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode typ domain codomain)) := by
  have hf := iffForward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.lambdaIff H M W raw domain child typ requested codomain gamma extended c hc ht he) ha
  have hs := OriginalTypedDecoderInternalListProof.consFields typ requested codomain (andLeft (andRight (andRight hf))) ht
  have heq : Nonempty (Derivation body Delta (eqn requested domain)) := by
    simpa only [equalEqn] using andLeft (andRight (andRight (andRight hf)))
  exact headTransport InternalListCodec.consCode typ requested domain (Fin.cons codomain Fin.elim0) heq hs

theorem lambdaTypeCases (H : Program 1) (M W : Program 2)
    (raw domain child typ gamma c : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (codomain : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (typ.relabel j) (domain.relabel j) codomain)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 3 → Program 3 := ![OriginalTypedDecoder.headOf (.projection 0),
    OriginalTypedDecoder.tailOf (.projection 0),(.composition InternalListCodec.consCode ![.projection 1,.projection 2])]
  let xs : Fin 3 → OTerm alpha := ![typ,domain,gamma]
  apply queryCases qs xs psi
  intro beta j ys Theta hj hq
  let xx : Fin 3 → OTerm beta := ![typ.relabel j,domain.relabel j,gamma.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        refine Fin.cases ?_ (fun k => Fin.elim0 k) i
        rfl
  rw [hx] at hq
  have ht := OriginalTypedDecoderInternalScalarProof.arrowFields (.projection 0) (typ.relabel j) (ys 0) (ys 1) xx (projectionValue 0 xx) (hq 0) (hq 1)
  have he := binaryRecover InternalListCodec.consCode (.projection 1) (.projection 2)
    (ys 2) (domain.relabel j) (gamma.relabel j) xx (hq 2) (projectionValue 1 xx) (projectionValue 2 xx)
  have hc' := renameInto hc j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph2Rename,termAcceptedRename] at hc' ha'
  exact next beta j Theta (ys 1) hj (lambdaFields H M W (raw.relabel j) (domain.relabel j) (child.relabel j) (typ.relabel j) (ys 0) (ys 1) (gamma.relabel j) (ys 2) (c.relabel j) hc' ht he ha')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTypeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTypeProof
