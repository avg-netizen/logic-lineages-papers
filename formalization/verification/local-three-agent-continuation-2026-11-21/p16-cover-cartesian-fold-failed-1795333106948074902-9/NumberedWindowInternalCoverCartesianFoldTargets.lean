module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalListMap (mapHead)
open ID1Completion.InternalRawListRecursion (listRec)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- The Cartesian axes are folded from the right. Each computed block
precedes the recursive tail in its original occurrence order. -/
def flatStep {k : Nat} (D : Program (k+1)) : Program (k+2) :=
  .composition append ![mapHead D,.projection 1]

def flatMap {k : Nat} (D : Program (k+1)) : Program (k+1) :=
  listRec (constantZero k) (flatStep D)

def collected {k : Nat} (D : Program (k+1)) : Program (k+2) :=
  .composition (flatMap D) (Fin.cons (.projection 0) (fun i => .projection i.succ.succ))

def containsImage {k : Nat} (D : Program (k+1)) : Program (k+2) :=
  .composition scratchMember ![collected D,.projection 1]

abbrev flatGraph {k : Nat} {α : Type} (D : Program (k+1)) (out raw : OTerm α) (params : Fin k → OTerm α) :=
  programGraph (flatMap D) out (Fin.cons raw params)

abbrev imageGraph {k : Nat} {α : Type} (D : Program (k+1)) (raw image : OTerm α) (params : Fin k → OTerm α) :=
  programGraph (containsImage D) (suc z) (Fin.cons raw (Fin.cons image params))

def ExactCartesianFoldValue : Prop := ∀ {k : Nat} (D : Program (k+1))
    (F : Nat → List.Vector Nat k → List Nat),
  (∀ a params, evaluate D (a ::ᵥ params) = numbersNumber (F a params)) →
  ∀ source params, evaluate (flatMap D) (numbersNumber source ::ᵥ params) =
    numbersNumber (source.flatMap fun a => F a params)

/-- A selected element and the member of its actual generated block are
preserved in the actual ordered scratch output. The programs and all
object-language terms can be open. -/
def ExactOpenCartesianFoldMember : Prop := ∀ {k : Nat} (D : Program (k+1))
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw source block image out : OTerm α) (params : Fin k → OTerm α),
  Nonempty (Derivation body Γ (memberGraph raw source)) →
  Nonempty (Derivation body Γ (programGraph D block (Fin.cons source params))) →
  Nonempty (Derivation body Γ (memberGraph block image)) →
  Nonempty (Derivation body Γ (flatGraph D out raw params)) →
  Nonempty (Derivation body Γ (memberGraph out image))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldTargets
