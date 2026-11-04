module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformFiberProof
open Source ContextUniform

theorem actualOriginalContextFibers : ContextUniformTargets.ActualOriginalContextFibers := by
  intro n arity Gamma context x y
  refine ⟨?_,?_,?_,?_⟩
  · simp [encodedScalar,objectCode]
  · simp [encodedList,objectCode]
  · simp [encodedR,objectCode]
  · simp [encodedDirect,objectCode]

theorem actualNoCrossContextEdges : ContextUniformTargets.ActualNoCrossContextEdges := by
  intro n arity Gamma Delta context x y hne
  constructor
  · rintro ⟨Xi,a,b,hx,hy,hr⟩
    simp only [objectCode,Encodable.encodek,Option.some.injEq,Prod.mk.injEq] at hx hy
    exact hne (hx.1.trans hy.1.symm)
  · rintro ⟨Xi,a,b,hx,hy,hr⟩
    simp only [objectCode,Encodable.encodek,Option.some.injEq,Prod.mk.injEq] at hx hy
    exact hne (hx.1.trans hy.1.symm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformFiberProof
