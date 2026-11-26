module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Acyclic pre-minimum input. Only the original source/target leaves are
made transparent; no newly constructed minimum or final traversal occurs. -/
def prior (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalTransparentDecoderSelection.transparentInputs H G W p

/-- The already checked total structural traversal at the prior input. -/
def core (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
  OriginalLambdaTraversalSelection.canonical (prior p H G W).base p.window

/-- The literal original active branch, including its existing source test. -/
def active (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
  OriginalFunctionNeutrality.active
    (OriginalLambdaTraversalSelection.transparentData (prior p H G W).base) p.window

/-- K keeps the complete prior representative on inactive vectors. This
is the PRE-refinement traversal, never the later minimum's own key. -/
def key (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
  OriginalLambdaTraversalSelection.representative (prior p H G W).base p.window

/-- Only the old representative changes after original decoder preparation.
The entire subsequent minimum/final pipeline receives this one input tuple. -/
def inputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    GlobalSourcePackage.Inputs :=
  { prior p H G W with base :=
    { (prior p H G W).base with oldRepresentative := key p H G W } }

def Active {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (value parameter : OTerm alpha) : Formula alpha :=
  graph2 (active p H G W) InternalOriginalStepGuard.one value parameter

/-- Independent actual-graph agreement on the existing active branch. -/
def ActiveCoreLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (value out parameter : OTerm alpha),
  Nonempty (Derivation body Delta ((Active p H G W value parameter).imp
    ((graph2 (key p H G W) out value parameter).iff
      (graph2 (core p H G W) out value parameter))))

/-- Two actual applications with shared structural child values have equal
K outputs. Only literal selector/active graphs are premises; no parent key
coherence, parent-output equality, successful-run or calibration is assumed. -/
def ApplicationCongruenceLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (value other d e fn arg otherFn otherArg fOut aOut out otherOut parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Active p H G W value parameter ⊓
      (Active p H G W other parameter ⊓
        (OriginalLambdaTraversalInternal.ApplicationFields value d e fn arg ⊓
          (OriginalLambdaTraversalInternal.ApplicationFields other d e otherFn otherArg ⊓
            (graph2 (core p H G W) fOut fn parameter ⊓
              (graph2 (core p H G W) fOut otherFn parameter ⊓
                (graph2 (core p H G W) aOut arg parameter ⊓
                  (graph2 (core p H G W) aOut otherArg parameter ⊓
                    (graph2 (key p H G W) out value parameter ⊓
                      graph2 (key p H G W) otherOut other parameter))))))))).imp
      (equal out otherOut)))

/-- Lambda congruence retains the SAME actual child parameter on both
sides. Its construction is in the original LambdaFields graphs, not a
replacement global Gamma or an external decoded environment. -/
def LambdaCongruenceLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (value other d e rawBody otherBody bodyOut out otherOut parameter childParameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Active p H G W value parameter ⊓
      (Active p H G W other parameter ⊓
        (OriginalLambdaTraversalInternal.LambdaFields value d e rawBody parameter childParameter ⊓
          (OriginalLambdaTraversalInternal.LambdaFields other d e otherBody parameter childParameter ⊓
            (graph2 (core p H G W) bodyOut rawBody childParameter ⊓
              (graph2 (core p H G W) bodyOut otherBody childParameter ⊓
                (graph2 (key p H G W) out value parameter ⊓
                  graph2 (key p H G W) otherOut other parameter))))))).imp
      (equal out otherOut)))

/- These are structural-key suppliers. Full preservation of this key by a
NEW minimum/final traversal, arbitrary-cutoff erasure, canonical cancellation,
internal I/C and the paper accessibility endpoint are separate obligations. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyDefinitions
