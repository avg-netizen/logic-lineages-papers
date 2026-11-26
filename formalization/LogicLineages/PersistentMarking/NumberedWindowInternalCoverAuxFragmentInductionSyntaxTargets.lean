module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentGuardTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalStrongInduction (below)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)

/-- The same actual context, key, and result on both original graph tapes. -/
def forwardClause {α : Type} (P Q : Program 3) (ctx result raw : OTerm α) : Formula α :=
  (windowAt P ctx result raw).imp (windowAt Q ctx result raw)

/-- The child result coordinate varies under a genuine finite universal.
The lexical context and raw key stay the same free object terms. -/
def forwardMatrix {α : Type} (P Q : Program 3) (ctx raw : OTerm α) : Formula (α ⊕ Fin 1) :=
  forwardClause P Q (ctx.relabel Sum.inl) (.var (.inr 0)) (raw.relabel Sum.inl)

def forwardAt {α : Type} (P Q : Program 3) (ctx raw : OTerm α) : Formula α :=
  (unary fragmentGuard (suc z) raw).imp (allBlock (forwardMatrix P Q ctx raw))

def forwardMotive {α : Type} (P Q : Program 3) (ctx : OTerm α) : Formula (α ⊕ Fin 1) :=
  forwardAt P Q (ctx.relabel Sum.inl) (.var (.inr 0))

abbrev forwardBelow {α : Type} (P Q : Program 3) (ctx raw : OTerm α) : Formula α :=
  below (forwardMotive P Q ctx) raw

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets
