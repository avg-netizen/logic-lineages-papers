module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransitionStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjection.Targets
open CotreePresburgerTransition

/-- Finite linear substitution counts actual list occurrences, including repeats. -/
def ProjectedWordCounts : Prop :=
  ∀ (Q A : Type) [Fintype Q] [LinearOrder Q] [Fintype A] [LinearOrder A]
    (label : A → Finset Q) (children : List A) B,
    projectedCounts label (fun a => children.count a) B = (children.map label).count B

def WordTotalCounts : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (children : List A),
    (∑ a, children.count a) = children.length

def AllowedWordCounts : Prop :=
  ∀ (A : Type) [DecidableEq A] (allowed : A → Bool) (children : List A),
    (∀ a, allowed a = false → children.count a = 0) ↔
      ∀ a ∈ children, allowed a = true

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjection.Targets
