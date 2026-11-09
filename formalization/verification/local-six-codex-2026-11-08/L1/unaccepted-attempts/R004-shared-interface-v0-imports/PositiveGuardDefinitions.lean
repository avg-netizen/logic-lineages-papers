module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuard
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All raw positive inputs stay [source,target,ORIGINAL path code,parameter].
Both endpoints use the SAME measure AST; no certificate field is added. -/
def markAt (measure : Program 1) (endpoint : Fin 4) : Program 4 :=
  .composition measure (fun _ : Fin 1 => .projection endpoint)

def flagAt (measure : Program 1) (endpoint : Fin 4) : Program 4 :=
  leftOf (markAt measure endpoint)

def depthAt (measure : Program 1) (endpoint : Fin 4) : Program 4 :=
  rightOf (markAt measure endpoint)

def spineTest (measure : Program 1) (endpoint : Fin 4) : Program 4 :=
  InternalApplicationStepPeel.same (flagAt measure endpoint) (InternalLessThan.constantOne 4)

/-- The target depth is the FIRST ltTest argument. -/
def depthLess (measure : Program 1) : Program 4 :=
  .composition InternalLessThan.ltTest
    (Fin.cons (depthAt measure 1) (Fin.cons (depthAt measure 0) Fin.elim0))

/-- Only true bottom-spine sources require a flagged target and strict
depth decrease. Exact-one normalization pays the arbitrary internal test
range, rather than assuming every symbolic flag is zero or one. -/
def spineGuard (measure : Program 1) : Program 4 :=
  InternalAcceptance.branch (InternalAcceptance.normalize (spineTest measure 0))
    (InternalLessThan.constantOne 4)
    (InternalAcceptance.conjunction (spineTest measure 1) (depthLess measure))

def bottomAt (bottom : Program 1) : Program 4 :=
  .composition bottom (fun _ : Fin 1 => .projection 0)

/-- A separate literal-bottom rejection remains convenient for the source
bottom introduction; it is natively redundant on every accepted old path. -/
def nonBottomGuard (bottom : Program 1) : Program 4 :=
  InternalAcceptance.branch (InternalAcceptance.normalize (bottomAt bottom))
    (InternalLessThan.constantOne 4) (InternalAcceptance.constantZero 4)

/-- Guard only the FINAL raw positive checker. The original edge checker,
reflexive suffix checker, pathMap and edgeLift Programs stay unchanged. -/
def checker (bottom measure : Program 1) (edge : Program 4) : Program 4 :=
  InternalAcceptance.conjunction (nonBottomGuard bottom)
    (InternalAcceptance.conjunction (spineGuard measure)
      (InternalParameterizedPathChecker.checker edge true))

def accepted {α : Type} (bottom measure : Program 1) (edge : Program 4)
    (x y certificate parameter : OTerm α) : Formula α :=
  graph4 (checker bottom measure edge) InternalOriginalStepGuard.one x y certificate parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuard
