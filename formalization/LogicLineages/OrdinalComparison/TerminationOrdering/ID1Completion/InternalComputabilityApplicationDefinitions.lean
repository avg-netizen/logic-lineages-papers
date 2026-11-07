module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplication
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Substitute symbolic context and object terms into the ORIGINAL finite
type recursion. The higher-type negative predicate occurrences are retained. -/
def computable {α : Type} (data : JointGammaComputability.Data) (tau : Ty)
    (context t : OTerm α) : Formula α :=
  (JointGammaComputability.formula data tau).subst
    ![arithmeticEmbedding.onTerm context,arithmeticEmbedding.onTerm t]

/-- Literal output-one graph of the original typed checker. -/
def typed {α : Type} (data : JointGammaComputability.Data) (tau : Ty)
    (context t : OTerm α) : Formula α :=
  programGraph data.typed (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    ![context,numeral (typeNumber tau),t]

/-- Literal original same-Gamma guard, without a replacement context code. -/
def guarded {α : Type} (data : JointGammaComputability.Data) (f a : OTerm α) : Formula α :=
  programGraph data.guard (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![f,a]

def arguments {α : Type} (context : OTerm α) (sigma tau : Ty) (f a : OTerm α) : Fin 5 → OTerm α :=
  ![context,numeral (typeNumber sigma),numeral (typeNumber tau),f,a]

/-- The original application graph on the same six input coordinates. -/
def accepted {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a out : OTerm α) : Formula α :=
  programGraph data.application (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    (InternalApplication.inputs (arguments context sigma tau f a) out)

/-- The object-language application witness keeps its computability conjunct. -/
def resultBody {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α) : Formula (α ⊕ Fin 1) :=
  accepted data sigma tau (context.relabel Sum.inl) (f.relabel Sum.inl)
      (a.relabel Sum.inl) (.var (.inr 0)) ⊓
    computable data tau (context.relabel Sum.inl) (.var (.inr 0))

def resultExists {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α) : Formula α :=
  existsOne (resultBody data sigma tau context f a)

def premises {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α) : Formula α :=
  computable data (.arrow sigma tau) context f ⊓
    (guarded data f a ⊓ computable data sigma context a)

/-- Only the original valid-window and numeric arrow-code graph facts.
Typedness and the same-context guard are supplied by the computability premises. -/
def metadata {α : Type} (window : Program 1) (arrow : Program 2)
    (context : OTerm α) (sigma tau : Ty) : Formula α :=
  programGraph window (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![context] ⊓
    programGraph arrow (numeral (typeNumber (.arrow sigma tau)))
      ![numeral (typeNumber sigma),numeral (typeNumber tau)]

def activationAt {α : Type} (data : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (context : OTerm α) (sigma tau : Ty)
    (f a : OTerm α) : Formula α :=
  programGraph (ApplicationDomain.activation window data.typed data.guard arrow)
    (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) (arguments context sigma tau f a)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplication
