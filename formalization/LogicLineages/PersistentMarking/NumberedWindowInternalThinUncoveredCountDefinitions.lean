module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCount
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalRawListRecursion (listRec)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

/-- The original auxiliary potential counts each uncovered occurrence in
the genuine vertices tape, preserving duplicates and original order. -/
def countStep : Program 3 :=
  branch (normalize (.composition scratchMember ![.projection 2,.projection 0]))
    (.composition .succ (fun _ : Fin 1 => .projection 1)) (.projection 1)

def count : Program 2 := listRec (constantZero 1) countStep

def bounded {α : Type} (small large : OTerm α) : Formula α :=
  ltF small large ⊔ eqn small large
end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCount
