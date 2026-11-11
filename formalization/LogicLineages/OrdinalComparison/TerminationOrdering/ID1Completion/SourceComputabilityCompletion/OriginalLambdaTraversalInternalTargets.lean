module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalLambdaTraversal OriginalLambdaTraversalInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Structural visits at literal raw tags, independently of any leaf or
source calibration. The SAME parameter travels with both application
children; the lambda expansion uses its actual childParameter Program. -/
def ActualOriginalLambdaTraversalInternalVisits : Prop :=
  ∀ (positive : Positive (Fin 1)) (leaf : Program 2) (alpha : Type)
    (Delta : List (Formula alpha)) (value parameter work results state out : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph4 visitState state value parameter work results ⊓
      graph1 rawTag (SourceComputabilityFormulaSupportProof.numeral 2) value).imp
      ((graph1 (transition leaf) out state).iff
        (graph4 applicationExpandedState out value parameter work results)))) ∧
  Nonempty (Derivation positive Delta
    ((graph4 visitState state value parameter work results ⊓
      graph1 rawTag InternalOriginalStepGuard.one value).imp
      ((graph1 (transition leaf) out state).iff
        (graph4 lambdaExpandedState out value parameter work results))))

/-- The other-tag leaf uses its own actual two-input graph, without a
Boolean, semantic or representative condition on the returned value. -/
def ActualOriginalLambdaTraversalInternalLeafStep : Prop :=
  ∀ (positive : Positive (Fin 1)) (leaf : Program 2) (alpha : Type)
    (Delta : List (Formula alpha)) (value parameter work results state produced out : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph4 visitState state value parameter work results ⊓
      (graph1 otherTag InternalOriginalStepGuard.one value ⊓
        graph2 leaf produced value parameter)).imp
      ((graph1 (transition leaf) out state).iff
        (graph3 returnState out produced work results))))

/-- Raw constructor graph laws at both return kinds. Child outputs are
arbitrary arithmetic terms; their outer types and sizes are unrestricted. -/
def ActualOriginalLambdaTraversalInternalReturns : Prop :=
  ∀ (positive : Positive (Fin 1)) (leaf : Program 2) (alpha : Type)
    (Delta : List (Formula alpha)),
  (∀ d e work argument function results state produced out : OTerm alpha,
    Nonempty (Derivation positive Delta
      ((programGraph applicationReturnState state ![d,e,work,argument,function,results] ⊓
        graph4 application produced d e function argument).imp
        ((graph1 (transition leaf) out state).iff
          (graph3 returnState out produced work results))))) ∧
  (∀ d e work body results state produced out : OTerm alpha,
    Nonempty (Derivation positive Delta
      ((programGraph lambdaReturnState state ![d,e,work,body,results] ⊓
        graph3 OriginalLambdaConstructor.constructor produced d e body).imp
        ((graph1 (transition leaf) out state).iff
          (graph3 returnState out produced work results)))))

/-- Empty work preserves the entire result stack, not merely its head. -/
def ActualOriginalLambdaTraversalInternalEmpty : Prop :=
  ∀ (positive : Positive (Fin 1)) (leaf : Program 2) (alpha : Type)
    (Delta : List (Formula alpha)) (results state out : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph1 emptyState state results).imp
      ((graph1 (transition leaf) out state).iff (equal out state))))

/-- The exact initialized bounded run has live empty work and a singleton
result, derived internally for arbitrary leaf/input/parameter. There is no
successful-run or external termination premise. -/
def ActualOriginalLambdaTraversalInternalRunShape : Prop :=
  ∀ (positive : Positive (Fin 1)) (leaf : Program 2) (alpha : Type)
    (Delta : List (Formula alpha)) (state value parameter : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 (run leaf) state value parameter).imp (FinishedRun state)))

/-- Full bounded application recurrence at the SAME fold, using actual raw
selector and child graphs. No source validity, guard, child success, bound,
canonicality or calibration assumption is supplied. -/
def ActualOriginalLambdaTraversalInternalApplication : Prop :=
  ∀ (positive : Positive (Fin 1)) (leaf : Program 2) (alpha : Type)
    (Delta : List (Formula alpha))
    (value d e fn arg functionOut argumentOut out parameter : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((ApplicationFields value d e fn arg ⊓
      (graph2 (fold leaf) functionOut fn parameter ⊓
        graph2 (fold leaf) argumentOut arg parameter)).imp
      ((graph2 (fold leaf) out value parameter).iff
        (graph4 application out d e functionOut argumentOut))))

/-- Full lambda recurrence with the ACTUAL original extended-Gamma
parameter. The body output is a graph of this SAME fold, never an earlier
fold or a body-computability/normalization hypothesis. Raw malformed lambda
fields remain permitted by the total selector specification. -/
def ActualOriginalLambdaTraversalInternalLambda : Prop :=
  ∀ (positive : Positive (Fin 1)) (leaf : Program 2) (alpha : Type)
    (Delta : List (Formula alpha))
    (value d e body bodyOut out parameter bodyParameter : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((LambdaFields value d e body parameter bodyParameter ⊓
      graph2 (fold leaf) bodyOut body bodyParameter).imp
      ((graph2 (fold leaf) out value parameter).iff
        (graph3 OriginalLambdaConstructor.constructor out d e bodyOut))))

/-- Only nonapplication/nonlambda tags use the selected leaf; the two
graphs agree in BOTH directions for arbitrary outputs and parameters. -/
def ActualOriginalLambdaTraversalInternalLeaf : Prop :=
  ∀ (positive : Positive (Fin 1)) (leaf : Program 2) (alpha : Type)
    (Delta : List (Formula alpha)) (value out parameter : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph1 otherTag InternalOriginalStepGuard.one value).imp
      ((graph2 (fold leaf) out value parameter).iff (graph2 leaf out value parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalTargets
