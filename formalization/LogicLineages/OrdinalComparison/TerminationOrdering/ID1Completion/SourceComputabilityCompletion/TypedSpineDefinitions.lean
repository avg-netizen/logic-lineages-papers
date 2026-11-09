module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpine
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original Object payload is its original right coordinate. The
ambient Gamma remains in its original left coordinate; it is not decoded
or fixed by this predicate. -/
def objectMeasure : Program 1 :=
  .composition BottomSpineMeasure.measure (fun _ : Fin 1 => InternalUnpair.right)

/-- Actual graph witnesses, not a semantic source-shape assertion. The
arbitrary mark is the full literal pair(flag,original spineDepth). -/
def marked {α : Type} (x mark depth : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 objectMeasure mark x ⊓
    (graph1 InternalUnpair.left InternalOriginalStepGuard.one mark ⊓
      graph1 InternalUnpair.right depth mark)

/-- The current depth is the distinguished induction variable. The object
and mark are quantified INSIDE it, so all source successors may vary. This
formula lives in the ONE original combined source calculus. -/
def depthBody {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (tau : Source.Ty) (depth : OrdinaryArithmetic.Term α) : Formula (α ⊕ Fin 2) :=
  (InternalComputabilityApplication.typed comp tau
      (SourceComputabilityFormulaSupportProof.numeral context) (.var (.inr 0)) ⊓
    marked (.var (.inr 0)) (.var (.inr 1)) (depth.relabel Sum.inl)).imp
    (InternalAccessibilityRules.membership false (.var (.inr 0)))

def atDepth {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (tau : Source.Ty) (depth : OrdinaryArithmetic.Term α) : Formula α :=
  InternalClosedPrograms.allBlock (depthBody comp context tau depth)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpine
