module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

abbrev appendGraph {α : Type} (out raw suffix : OTerm α) :=
  programGraph append out ![raw,suffix]

def appendCall : Program 3 := .composition append ![.projection 0,.projection 1]

def appendMember : Program 3 := .composition scratchMember ![appendCall,.projection 2]

abbrev tested {α : Type} (raw suffix k : OTerm α) :=
  programGraph appendMember (suc z) ![raw,suffix,k]

abbrev appears {α : Type} (raw suffix k : OTerm α) :=
  memberGraph raw k ⊔ memberGraph suffix k

abbrev atList {α : Type} (raw suffix k : OTerm α) :=
  (appears raw suffix k).imp (tested raw suffix k)

abbrev motive {α : Type} (suffix k : OTerm α) : Formula (α ⊕ Fin 1) :=
  atList (.var (.inr 0)) (suffix.relabel Sum.inl) (k.relabel Sum.inl)

/-- Either physical input occurrence survives in the literal append output.
This claim does not use the surrounding original-primary runtime theory. -/
def ExactOpenScratchAppendMembership : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw suffix out k : OTerm α),
    Nonempty (Derivation body Γ (appendGraph out raw suffix)) →
    Nonempty (Derivation body Γ (appears raw suffix k)) →
    Nonempty (Derivation body Γ (memberGraph out k))

end LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenTargets
