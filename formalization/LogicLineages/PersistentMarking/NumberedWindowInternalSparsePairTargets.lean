module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair
public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalLessThan (strictLess)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePair (pairTerm fieldCons)

def PairValue : Prop :=
  ∀ x y, evaluate NumberedWindowInternalSparsePair.pair (x ::ᵥ y ::ᵥ nil) =
    NumberedWindowPairAlgorithm.pair x y

def FieldConsValue : Prop :=
  ∀ x tail, evaluate fieldCons (x ::ᵥ tail ::ᵥ nil) =
    NumberedWindowPairAlgorithm.pair x tail + 1

def OpenPairGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x y : OTerm α),
    let graph := programGraph NumberedWindowInternalSparsePair.pair out ![x,y]
    let equation := equal out (pairTerm x y)
    Nonempty (Derivation body [] ((graph.imp equation) ⊓ (equation.imp graph)))

def OpenFieldConsGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x tail : OTerm α),
    let graph := programGraph fieldCons out ![x,tail]
    let equation := equal out (OrdinaryArithmetic.succTerm (pairTerm x tail))
    Nonempty (Derivation body [] ((graph.imp equation) ⊓ (equation.imp graph)))

/-- An actual object proof of injectivity with arbitrary open terms and a
shared output. There is no evaluation-based arithmetic rule. -/
def OpenPairInjective : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x y u v : OTerm α),
    let P := programGraph NumberedWindowInternalSparsePair.pair out ![x,y]
    let Q := programGraph NumberedWindowInternalSparsePair.pair out ![u,v]
    Nonempty (Derivation body [] ((P ⊓ Q).imp (equal x u ⊓ equal y v)))

def OpenFieldConsInjective : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x y u v : OTerm α),
    let P := programGraph fieldCons out ![x,y]
    let Q := programGraph fieldCons out ![u,v]
    Nonempty (Derivation body [] ((P ⊓ Q).imp (equal x u ⊓ equal y v)))

/-- A genuine cons cannot be zero, and its raw tail is strictly smaller in
the existing object order. This does not assert that any nonzero number is
a genuine cons; sparse malformed inputs will remain a separate decoder case. -/
def OpenFieldConsTailDecrease : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x tail : OTerm α),
    let graph := programGraph fieldCons out ![x,tail]
    Nonempty (Derivation body [] (graph.imp
      ((equal out OrdinaryArithmetic.zeroTerm).not ⊓ strictLess tail out)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairTargets
