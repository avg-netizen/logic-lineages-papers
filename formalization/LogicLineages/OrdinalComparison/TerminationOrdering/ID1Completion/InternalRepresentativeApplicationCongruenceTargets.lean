module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalRepresentativeApplicationCongruence
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual valid representative wrapper keeps exactly the old Program's
right payload. This is INTERNAL for arbitrary Programs, formulas and symbolic
terms, with neither calibration nor equality of the whole outputs assumed. -/
def ActualOriginalRepresentativePayloadTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (valid oldRepresentative : Program 1)
    (α : Type) (payload out raw : OTerm α),
  Nonempty (Derivation body []
    ((InternalRepresentativeTag.representation valid oldRepresentative out raw).imp
      ((graph1 InternalUnpair.right payload out).iff
        (graph1 (rightOf oldRepresentative) payload raw))))

/-- Source-side LOCAL application congruence for the actual selected wrapper.
The premise carries child success, source-valid function and parent, literal
constructor graphs, a fixed actual argument and actual combine output. The
conclusion retains parent success and the SAME output of the source wrapper.
Root validity is an explicit later closure obligation, not congruence itself. -/
def ActualOriginalCertifiedSourceRepresentativeApplicationCongruence : Prop :=
  ∀ (body : Positive (Fin 1)) (validity : InternalOriginalStepGuard.Data)
    (member : Program 1) (old : InternalQuotientEdgeChecker.Data) (α : Type)
    (arrow d e fp ap fn arg parent x out : OTerm α),
  Nonempty (Derivation body []
    ((graph1 (data validity member old).sourceRepresentative x fn ⊓
      applicationPremises validity member old arrow d e fp ap fn arg parent x out).imp
      (graph1 (goodRun validity member old) InternalOriginalStepGuard.one parent ⊓
        graph1 (data validity member old).sourceRepresentative out parent)))

/-- Target-side LOCAL application congruence at the same source-valid opened
root. This is not unrestricted target dispatch: source validity of fn and
parent stays explicit. It concludes the exact target wrapper at the SAME
combine output, without assuming a type invariant or x=N(fn). -/
def ActualOriginalCertifiedTargetRepresentativeApplicationCongruence : Prop :=
  ∀ (body : Positive (Fin 1)) (validity : InternalOriginalStepGuard.Data)
    (member : Program 1) (old : InternalQuotientEdgeChecker.Data) (α : Type)
    (arrow d e fp ap fn arg parent x out : OTerm α),
  Nonempty (Derivation body []
    ((graph1 (data validity member old).targetRepresentative x fn ⊓
      applicationPremises validity member old arrow d e fp ap fn arg parent x out).imp
      (graph1 (goodRun validity member old) InternalOriginalStepGuard.one parent ⊓
        graph1 (data validity member old).targetRepresentative out parent)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceTargets
