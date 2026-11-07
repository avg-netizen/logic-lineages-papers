module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplication
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Lift exactly the first five inputs. The result coordinate never controls activation. -/
def firstFive (p : Program 5) : Program 6 :=
  .composition p (fun i => .projection i.castSucc)

/-- Compare the raw output coordinate with the total builder output. -/
def resultCheck (result : Program 5) : Program 6 :=
  .composition InternalEqualityTest.equalityTest ![.projection 5,firstFive result]

/-- Inactive inputs retain the ORIGINAL application checker value unchanged. -/
def application (active result : Program 5) (old : Program 6) : Program 6 :=
  InternalAcceptance.branch (firstFive active) old (resultCheck result)

def computability (old : JointGammaComputability.Data) (window : Program 1)
    (arrow : Program 2) (result : Program 5) : JointGammaComputability.Data :=
  { old with application := application (ApplicationDomain.activation window old.typed old.guard arrow) result old.application }

/-- Literal original application formula; this is not a replacement semantics. -/
def literalApplication {α : Type} (p : Program 6) (context : Nat) (sigma tau : Ty)
    (f a out : OTerm α) : Formula α :=
  arithmeticEmbedding.onFormula ((JointGammaApplication.applicationFormula p).subst
    ![numeral context,numeral (typeNumber sigma),numeral (typeNumber tau),f,a,out])

/-- One output coordinate after the unchanged first five inputs. -/
def inputs {X : Type} (xs : Fin 5 → X) (out : X) : Fin 6 → X :=
  ![xs 0,xs 1,xs 2,xs 3,xs 4,out]

def applicationExists {α : Type} (p : Program 6) (xs : Fin 5 → OTerm α) : Formula α :=
  existsOne (programGraph p (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    (inputs (fun i => (xs i).relabel Sum.inl) (.var (.inr (0 : Fin 1)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplication
