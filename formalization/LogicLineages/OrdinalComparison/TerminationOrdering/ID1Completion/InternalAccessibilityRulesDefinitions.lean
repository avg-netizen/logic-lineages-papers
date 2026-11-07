module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRules
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Select the existing carrier checker; no new notion of typedness is used. -/
def carrierProgram (data : SourcePresentation.Data) : Bool → Program 2
  | false => data.scalar
  | true => data.multiset

/-- Select the original positive-path or direct-multiset certificate checker. -/
def edgeProgram (data : SourcePresentation.Data) : Bool → Program 4
  | false => data.positive
  | true => data.direct

def membership {α : Type} (odd : Bool) (x : OrdinaryArithmetic.Term α) : Formula α :=
  (Positive.predicate (tagTerm odd x)).formula

def carrier {α : Type} (data : SourcePresentation.Data) (odd : Bool) (context : Nat)
    (x : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula ((SourcePresentation.checkerFormula (carrierProgram data odd)).subst
    ![numeral context,x])

def edge {α : Type} (data : SourcePresentation.Data) (odd : Bool) (context : Nat)
    (x y : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula ((OrdinaryArithmeticQuotient.certificateGraph (edgeProgram data odd)).subst
    ![numeral context,x,y])

/-- The literal original accepting graph, with its certificate still explicit. -/
def certificate {α : Type} (data : SourcePresentation.Data) (odd : Bool) (context : Nat)
    (x y witness : OrdinaryArithmetic.Term α) : Formula α :=
  InternalControlGraph.programGraph (edgeProgram data odd)
    (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    ![numeral context,x,y,witness]

def successors {α : Type} (data : SourcePresentation.Data) (odd : Bool) (context : Nat)
    (x : OrdinaryArithmetic.Term α) : Formula α :=
  allOne
    ((edge data odd context (x.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (membership odd (.var (.inr (0 : Fin 1)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRules
