module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)

/-- Literal type-only leaf in the original leaves union, with no numeral
axis. Its own code is sparse; its containing singleton is standard scratch. -/
def typeLeafTerm {α : Type} (ty : OTerm α) : OTerm α :=
  rawCons (numeral 3) (rawCons ty z)

def typeLeafCode : Program 1 :=
  binary fieldCons (literal 1 3) (binary fieldCons (.projection 0) (constantZero 1))

def typeLeafSingleton : Program 1 := binary consCode typeLeafCode (constantZero 1)

def typeLeaves : Program 1 := flatMap (k := 0) typeLeafSingleton

abbrev unaryTape {α : Type} (x : OTerm α) : Fin 1 → OTerm α := Fin.cons x Fin.elim0

abbrev typeLeavesReport {α : Type} (out K : OTerm α) : Formula α :=
  programGraph typeLeaves out (unaryTape K)

def ExactCoverTypeLeavesValue : Prop :=
  ∀ (K : List Nat), evaluate typeLeaves (numbersNumber K ::ᵥ nil) =
    numbersNumber (K.map fun ty => packNode 3 [ty])

def ExactOpenCoverTypeLeavesConstructor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out K ty : OTerm α),
  Nonempty (Derivation body Γ (typeLeavesReport out K)) →
  Nonempty (Derivation body Γ (memberGraph K ty)) →
  Nonempty (Derivation body Γ (memberGraph out (typeLeafTerm ty)))

abbrev typeLeafOriginRow {α : Type} (K key ty : OTerm α) : Formula α :=
  memberGraph K ty ⊓ eqn (typeLeafTerm ty) key

abbrev typeLeafOriginBinder {α : Type} (K key : OTerm α) : Formula (α ⊕ Fin 1) :=
  typeLeafOriginRow (K.relabel Sum.inl) (key.relabel Sum.inl) (.var (.inr 0))

abbrev typeLeafOrigin {α : Type} (K key : OTerm α) : Formula α :=
  existsOne (typeLeafOriginBinder K key)

def ExactOpenCoverTypeLeavesOrigin : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out K key : OTerm α),
  Nonempty (Derivation body Γ (typeLeavesReport out K)) →
  Nonempty (Derivation body Γ (memberGraph out key)) →
  Nonempty (Derivation body Γ (typeLeafOrigin K key))

def ExactOpenCoverTypeLeavesInclusion : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out next K : OTerm α),
  Nonempty (Derivation body Γ (typeLeavesReport out K)) →
  Nonempty (Derivation body Γ (typeLeavesReport next K)) →
  Nonempty (Derivation body Γ (axisInclusion out next))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
