module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountNilTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalProjectedCountLeftTargets (D)

abbrev project {α : Type} (out input : OTerm α) := unary scratchTargets (suc out) input
abbrev compared {α : Type} (p j : OTerm α) := observer permutation p j

def reportMatrix {α : Type} (code pool vl vr p pl pr j : OTerm α) : Formula α :=
  filterGraph true vl code pool ⊓ (filterGraph false vr code pool ⊓
    (project p code ⊓ (project pl vl ⊓ (project pr vr ⊓ appendGraph j pl pr))))

def consequent {α : Type} (code pool vl vr p pl pr j : OTerm α) : Formula α :=
  (reportMatrix code pool vl vr p pl pr j).imp (compared p j)

def matrix {α : Type} (code pool : OTerm α) : Formula (α ⊕ Fin 6) :=
  consequent (code.relabel Sum.inl) (pool.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))
    (.var (.inr 5))

def atRows {α : Type} (code pool : OTerm α) : Formula α := allBlock (matrix code pool)

abbrev motive {α : Type} (pool : OTerm α) : Formula (α ⊕ Fin 1) :=
  atRows (.var (.inr 0)) (pool.relabel Sum.inl)

def ExactOpenProjectedCount : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code pool vl vr p pl pr j : OTerm α),
    D B Γ (reportMatrix code pool vl vr p pl pr j) →
    D B Γ (compared p j)

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionTargets
