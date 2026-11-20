module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDownwardTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof ID1Completion.InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalDownwardTargets (ApplicationEdgeMatching)
open NumberedWindowInternalPresentationTargets (data)
abbrev OTerm := OrdinaryArithmetic.Term

def suppliedEdge {α : Type} (r : Program 3) (x y : OTerm α) : Formula α :=
  existsOne (accepts r (x.relabel Sum.inl) (.var (.inr 0)) (y.relabel Sum.inl))

def suppliedMatch {α : Type} (p r : Program 3) (f u v : OTerm α) : Formula α :=
  existsOne (accepts p (f.relabel Sum.inl) (u.relabel Sum.inl) (.var (.inr 0)) ⊓
    suppliedEdge r (.var (.inr 0)) (v.relabel Sum.inl))

/-- The input certificate w is explicit; both the earlier result and its
transformed certificate are existentially bound in the actual calculus. -/
def RawMatching (r p : Program 3) (body : PositiveArithmeticOperators.Positive (Fin 1)) : Prop :=
  ∀ (α : Type) (f g u v w : OTerm α), Nonempty (Derivation body []
    ((accepts r f w g ⊓ accepts p g u v).imp (suppliedMatch p r f u v)))

def MatchingReduction : Prop :=
  ∀ (i j : Program 1) (r d p : Program 3) (c : Nat),
    RawMatching r p (ID1Completion.SourcePresentation.sourceBody (data i j r d) c) →
    ApplicationEdgeMatching (data i j r d) p c

end LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionTargets
