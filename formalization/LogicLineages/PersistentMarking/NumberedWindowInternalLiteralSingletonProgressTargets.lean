module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonOriginTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchIntroTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (allOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode singletonJ scalarLower)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)

def singletonMembers {α : Type} (scratch : OTerm α) : Formula α :=
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((memberGraph (scratch.relabel Sum.inl) key).imp (singletonJ key))

/-- A genuine target fold with *local* already-proved singleton J per
actual member, not a global scalar-to-singleton promotion hypothesis. -/
def SingletonTargetFoldSupply (i : Program 1) (r : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (raw scratch : OTerm α),
    let S := literalData i r
    let B := sourceBody S c
    Nonempty (Derivation B Γ (unary parser (suc scratch) raw)) →
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) scratch)) →
    Nonempty (Derivation B Γ (singletonMembers scratch)) →
    Nonempty (Derivation B Γ (membership true raw))

def ExactLiteralSingletonCarrierFromScalar : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    let S := literalData i r
    let B := sourceBody S c
    Nonempty (Derivation B Γ (carrier S false c q)) →
    Nonempty (Derivation B Γ (carrier S true c (singletonCode q)))

def ExactLiteralSingletonLowerMembers : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat) (α : Type) (Γ : List (Formula α))
    (head dst w decoded : OTerm α),
    let S := literalData i r
    let B := sourceBody S c
    Nonempty (Derivation B Γ (scalarLower S c head)) →
    Nonempty (Derivation B Γ (certificate S true c (singletonCode head) dst w)) →
    Nonempty (Derivation B Γ (unary parser (suc decoded) dst)) →
    Nonempty (Derivation B Γ (singletonMembers decoded))

def ExactLiteralSingletonPromotionFromFold : Prop :=
  ∀ (i : Program 1) (r : Program 3) (c : Nat), SingletonTargetFoldSupply i r c →
    ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    Nonempty (Derivation (sourceBody (literalData i r) c) Γ
      ((membership false q).imp (singletonJ q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressTargets
