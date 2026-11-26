module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternal
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact complement of the two structural term tags, at every raw input. -/
def otherTag : Program 1 :=
  InternalAcceptance.branch (InternalApplicationStepPeel.same rawTag (two 1))
    (InternalAcceptance.branch (OriginalHereditaryValidity.exactOne rawTag)
      (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1))
    (InternalAcceptance.constantZero 1)

/-- Inputs [raw value,its parameter,work suffix,whole result stack]. -/
def visitState : Program 4 := liveOf
  (consOf (visitOf (.projection 0) (.projection 1)) (.projection 2)) (.projection 3)

def applicationExpandedState : Program 4 := liveOf
  (consOf (visitOf (.composition rawFunction (fun _ : Fin 1 => .projection 0)) (.projection 1))
    (consOf (visitOf (.composition rawArgument (fun _ : Fin 1 => .projection 0)) (.projection 1))
      (consOf (applicationReturnOf
        (.composition rawDomain (fun _ : Fin 1 => .projection 0))
        (.composition rawType (fun _ : Fin 1 => .projection 0))) (.projection 2))))
  (.projection 3)

def lambdaExpandedState : Program 4 := liveOf
  (consOf (visitOf (.composition rawBody (fun _ : Fin 1 => .projection 0))
      (.composition childParameter ![.projection 0,.projection 1]))
    (consOf (lambdaReturnOf
      (.composition rawDomain (fun _ : Fin 1 => .projection 0))
      (.composition rawCodomain (fun _ : Fin 1 => .projection 0))) (.projection 2)))
  (.projection 3)

/-- Inputs [domain,codomain,work suffix,argument,function,result suffix]. -/
def applicationReturnState : Program 6 := liveOf
  (consOf (applicationReturnOf (.projection 0) (.projection 1)) (.projection 2))
  (consOf (.projection 3) (consOf (.projection 4) (.projection 5)))

/-- Inputs [domain,codomain,work suffix,body,result suffix]. -/
def lambdaReturnState : Program 5 := liveOf
  (consOf (lambdaReturnOf (.projection 0) (.projection 1)) (.projection 2))
  (consOf (.projection 3) (.projection 4))

abbrev returnState := InternalApplicationResultStack.returnState
abbrev emptyState := InternalApplicationResultStack.emptyState
def finishedState : Program 1 := liveOf (InternalAcceptance.constantZero 1)
  (consOf (.projection 0) (InternalAcceptance.constantZero 1))

/-- Actual total selectors, including the literal tag. No source validity,
successful decoding, child run, fixedness or native calibration is hidden. -/
def ApplicationFields {alpha : Type}
    (value d e fn arg : OTerm alpha) : Formula alpha :=
  graph1 rawTag (SourceComputabilityFormulaSupportProof.numeral 2) value ⊓
    (graph1 rawDomain d value ⊓ (graph1 rawType e value ⊓
      (graph1 rawFunction fn value ⊓ graph1 rawArgument arg value)))

/-- These fields also cover malformed tag-one outer types: codomain and body
are the literal total selectors, and the returned lambda uses the original
constructor at d/e. Semantic validity is a separate later theorem. -/
def LambdaFields {alpha : Type}
    (value d e rawBody parameter bodyParameter : OTerm alpha) : Formula alpha :=
  graph1 rawTag InternalOriginalStepGuard.one value ⊓
    (graph1 rawDomain d value ⊓ (graph1 rawCodomain e value ⊓
      (graph1 OriginalLambdaTraversal.rawBody rawBody value ⊓
        graph2 childParameter bodyParameter value parameter)))

def FinishedRun {alpha : Type} (state : OTerm alpha) : Formula alpha :=
  SourceComputabilityFormulaSupportProof.existsOne
    (graph1 finishedState (state.relabel Sum.inl) (.var (.inr 0)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternal
