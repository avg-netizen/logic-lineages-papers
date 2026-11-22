module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (lambdas)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverNamedLeavesTargets (namedFromIds namedTerm)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)

/-- Literal old lambda grammar axes: unchanged K outer, actual child terms
inner. The existing positional tag/type/code emitter is specialized at tag
2, with source [child term,type]. No numeral-range call is executed. -/
def lambdaLayer : Program 2 := namedFromIds 2

abbrev lambdaTerm {α : Type} (ty q : OTerm α) := namedTerm 2 ty q

abbrev lambdaReport {α : Type} (out K children : OTerm α) : Formula α :=
  programGraph lambdaLayer out ![K,children]

def ExactCoverLambdaLayerValue : Prop :=
  ∀ (K children : List Nat),
    evaluate lambdaLayer (numbersNumber K ::ᵥ numbersNumber children ::ᵥ nil) =
      numbersNumber (lambdas K children)

def ExactOpenCoverLambdaLayerConstructor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out K children ty q : OTerm α),
  Nonempty (Derivation body Γ (lambdaReport out K children)) →
  Nonempty (Derivation body Γ (memberGraph K ty)) →
  Nonempty (Derivation body Γ (memberGraph children q)) →
  Nonempty (Derivation body Γ (memberGraph out (lambdaTerm ty q)))

abbrev lambdaOriginRow {α : Type} (K children key ty q : OTerm α) : Formula α :=
  memberGraph K ty ⊓ (memberGraph children q ⊓ eqn (lambdaTerm ty q) key)

abbrev lambdaOriginMatrix {α : Type} (K children key : OTerm α) : Formula (α ⊕ Fin 2) :=
  lambdaOriginRow (K.relabel Sum.inl) (children.relabel Sum.inl) (key.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))

abbrev lambdaOrigin {α : Type} (K children key : OTerm α) : Formula α :=
  block (lambdaOriginMatrix K children key)

def ExactOpenCoverLambdaLayerOrigin : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out K children key : OTerm α),
  Nonempty (Derivation body Γ (lambdaReport out K children)) →
  Nonempty (Derivation body Γ (memberGraph out key)) →
  Nonempty (Derivation body Γ (lambdaOrigin K children key))

/-- Both output reports use the very same original type scratch K. The
only transport premise is actual object inclusion on the child-term axis. -/
def ExactOpenCoverLambdaLayerTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (old next K children children' key : OTerm α),
  Nonempty (Derivation body Γ (lambdaReport old K children)) →
  Nonempty (Derivation body Γ (lambdaReport next K children')) →
  Nonempty (Derivation body Γ (axisInclusion children children')) →
  Nonempty (Derivation body Γ (memberGraph old key)) →
  Nonempty (Derivation body Γ (memberGraph next key))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
