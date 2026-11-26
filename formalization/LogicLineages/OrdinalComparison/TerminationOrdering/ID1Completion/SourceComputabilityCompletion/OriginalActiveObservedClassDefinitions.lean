module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClassDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClass
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph1 graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original window and transparent source, independent of any minimum. -/
def activation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
  let q := OriginalTransparentDecoderSelection.transparentInputs H G W p
  OriginalRankGuardedRepresentative.active q.base.oldSource q.window

/-- Outside the original active domain retain the complete original test.
Inside it, every nonreflexive hit checks the observer before minimization. -/
def classTest (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) : Program 3 :=
  InternalAcceptance.branch
    (.composition (activation p H G W) ![.projection 0,.projection 2])
    P (OriginalObservedClass.observed O P)

def HitLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed out parameter mark : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (activation p H G W) InternalOriginalStepGuard.one seed parameter ⊓
      OriginalTransparentMinimum.graph3
        (OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
          (classTest p H G W O P))
        InternalOriginalStepGuard.one seed out parameter).imp
      ((graph1 O mark out).iff (graph1 O mark seed))))

/-- The unchanged once-guarded representative, with active observer checks
inside its actual minimum. No new final fold or source predicate is used. -/
def inputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) : GlobalSourcePackage.Inputs :=
  OriginalTransparentMinimum.transparentInputs H G W
    (classTest p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P) p

/-- On the active original domain the post-scan rank guard is redundant
internally, so its actual output retains genuine least-hit minimality. -/
def GuardCollapseLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed out parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (OriginalTypedDecoder.target H G) InternalOriginalStepGuard.one seed parameter ⊓
      (graph2 (activation p H G W) InternalOriginalStepGuard.one seed parameter ⊓
        graph2 (inputs p H G W P).base.oldRepresentative out seed parameter)).imp
      (graph2 (OriginalTransparentMinimum.minimum (OriginalTypedDecoder.target H G)
        (classTest p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P))
        out seed parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClass
