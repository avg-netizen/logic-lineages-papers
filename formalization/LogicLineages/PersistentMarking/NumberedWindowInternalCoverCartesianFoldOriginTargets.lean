module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCartesianFoldTargets (flatGraph)

abbrev blockSelectors {k : Nat} : Fin (k+1) → Program (k+2) :=
  Fin.cons (.projection 0) (fun i => .projection i.succ.succ)

def blockCall {k : Nat} (D : Program (k+1)) : Program (k+2) :=
  .composition D blockSelectors

def testsBlock {k : Nat} (D : Program (k+1)) : Program (k+2) :=
  .composition scratchMember ![blockCall D,.projection 1]

abbrev blockHit {k : Nat} (D : Program (k+1)) {α : Type}
    (source image : OTerm α) (params : Fin k → OTerm α) : Formula α :=
  programGraph (testsBlock D) (suc z) (Fin.cons source (Fin.cons image params))

abbrev originRow {k : Nat} (D : Program (k+1)) {α : Type}
    (raw source image : OTerm α) (params : Fin k → OTerm α) : Formula α :=
  memberGraph raw source ⊓ blockHit D source image params

abbrev originBinder {k : Nat} (D : Program (k+1)) {α : Type}
    (raw image : OTerm α) (params : Fin k → OTerm α) : Formula (α ⊕ Fin 1) :=
  originRow D (raw.relabel Sum.inl) (.var (.inr 0)) (image.relabel Sum.inl)
    (fun i => (params i).relabel Sum.inl)

def hasOrigin {k : Nat} (D : Program (k+1)) {α : Type}
    (raw image : OTerm α) (params : Fin k → OTerm α) : Formula α :=
  existsOne (originBinder D raw image params)

/-- An actual hit in the literal ordered Cartesian fold has an object
source witness in the same physical input list. Replaying the same D at
that source and unchanged parameters, and testing the generated block,
returns exactly one for the same image. No uniqueness, independent
numerical evaluator, or grammar-layer transport is asserted. -/
def ExactOpenCartesianFoldOrigin : Prop := ∀ {k : Nat} (D : Program (k+1))
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw image out : OTerm α) (params : Fin k → OTerm α),
  Nonempty (Derivation body Γ (flatGraph D out raw params)) →
  Nonempty (Derivation body Γ (memberGraph out image)) →
  Nonempty (Derivation body Γ (hasOrigin D raw image params))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginTargets
