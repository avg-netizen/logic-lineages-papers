module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastSubstitutionThinProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Subst)

theorem leastSubst (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    {α β : Type} (ctx ty seed x : OTerm α) (ts : α → OTerm β) :
    (leastGraph C X W s ctx ty seed x).subst (fun a => emb (ts a)) =
      leastGraph C X W s (ctx.subst ts) (ty.subst ts) (seed.subst ts) (x.subst ts) := by
  simp only [leastGraph,graph3Subst,sucSubst]

#print axioms leastSubst
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastSubstitutionThinProof
