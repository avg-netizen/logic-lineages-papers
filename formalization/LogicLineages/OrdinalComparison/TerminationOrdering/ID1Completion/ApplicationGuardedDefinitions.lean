module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuarded
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

/-- Exactly the original typed function, typed argument and same-Gamma formulas. -/
def domain {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (sigma tau : Ty) (f a : OTerm α) : Formula α :=
  (GuardedSource.literalTyped comp context (numeral (typeNumber (.arrow sigma tau))) f ⊓
    GuardedSource.literalTyped comp context (numeral (typeNumber sigma)) a) ⊓
    GammaGuardedSource.literalGuard comp f a

/-- The existential retains the literal original application formula and free names. -/
def existsApplication {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (sigma tau : Ty) (f a : OTerm α) : Formula α :=
  existsOne (InternalApplication.literalApplication comp.application context sigma tau
    (f.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr (0 : Fin 1))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuarded
