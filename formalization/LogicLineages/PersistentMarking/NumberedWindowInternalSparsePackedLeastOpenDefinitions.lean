module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpen
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed packedLeastProgram)

/-- Successful output of the unchanged physical packed least program on
the literal tape [ctx,ty,seed]. The successor tag is the only success test. -/
def leastGraph {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α) : Formula α :=
  programGraph (packedLeastProgram C X W s) (suc selected) ![ctx,ty,seed]

/-- One physical tape in all three graphs' inputs. The pool is the actual
output of the same members program; the candidate is the same selected term. -/
def poolOccurrenceRow {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected contextPayload pool : OTerm α) : Formula α :=
  programGraph contextOption (suc contextPayload) ![ctx,ty,seed] ⊓
    (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ memberGraph pool selected)

/-- Two genuine object quantifiers: context payload outermost, then pool.
The free terms are lifted past both binders, so neither can be captured. -/
def poolOccurrence {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α) : Formula α :=
  let lift : OTerm α → OTerm ((α ⊕ Fin 1) ⊕ Fin 1) :=
    fun t => (t.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel Sum.inl
  existsOne (existsOne (poolOccurrenceRow C X W s (lift ctx) (lift ty) (lift seed) (lift selected)
    (.var (.inl (.inr 0))) (.var (.inr 0))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpen
