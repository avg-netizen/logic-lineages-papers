module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowKnowledgeDispatch
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatchProof
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowKnowledgeDispatchProof
open GorbowSyntax GorbowSortedRevision GorbowSortedSyntaxCode GorbowBooleanTruth
open GorbowSortedKnowledgeAxioms GorbowRegistryDispatch GorbowKnowledgeDispatch

theorem fixedClauses : Comparators.GorbowKnowledgeDispatch.FixedClauses := by
  intro g P
  refine ⟨?_,?_,?_⟩
  · exact ⟨0,rfl⟩
  · intro code _
    change (P code → ∀ a, a=0 → a=0 ∧ P code) ∧ ((∀ a, a=0 → a=0 ∧ P code) → P code)
    exact ⟨fun h a ha => ⟨ha,h⟩,fun h => (h 0 rfl).2⟩
  · intro a _ code _ h
    exact h.2

private theorem distributionInstance (g : Ground) (hr : RelationLaws g) (hf : FunctionLaws g) (P : Extension)
    (hP : ∀ φ ψ : Sentence, P (formulaCode φ) → P (formulaCode (.imp φ ψ)) → P (formulaCode ψ))
    (n : Nat) (a s t : Term n) ρ
    (ha : (Formula.agent a).realize (interpretation g P) ρ)
    (hs : (sentenceGuard s).realize (interpretation g P) ρ)
    (ht : (sentenceGuard t).realize (interpretation g P) ρ) :
    (Formula.imp (.conj (.knowledge a s) (.knowledge a (binaryCodeTerm 0 s t)))
      (.knowledge a t)).realize (interpretation g P) ρ := by
  obtain ⟨φ,hφ⟩ := (GorbowRegistryDispatchProof.Boolean.guardCalibration g hr hf n s P ρ).mp hs
  obtain ⟨ψ,hψ⟩ := (GorbowRegistryDispatchProof.Boolean.guardCalibration g hr hf n t P ρ).mp ht
  have hi := (GorbowRegistryDispatchProof.Boolean.functionCalibration g hr hf n s t P ρ φ ψ hφ hψ).2.1
  intro h
  change a.realize _ ρ=0 ∧ P (t.realize _ ρ)
  refine ⟨ha,?_⟩
  rw [hψ]
  apply hP φ ψ
  · simpa only [hφ] using h.1.2
  · simpa only [hi] using h.2.2

attribute [local irreducible] GorbowRegistryTuple.headerTerm GorbowRegistryTuple.pairTerm GorbowRegistryTuple.tupleTerm

theorem closureDistribution : Comparators.GorbowKnowledgeDispatch.ClosureDistribution := by
  intro g hr hf P h a ha p hp q hq
  have hv2 : Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)) (2 : Fin 3)=a := by
    change Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)) (0 : Fin 1).succ.succ=a
    rw [Fin.cases_succ,Fin.cases_succ,Fin.cases_zero]
  have hv1 : Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)) (1 : Fin 3)=p := by
    change Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)) (0 : Fin 2).succ=p
    rw [Fin.cases_succ,Fin.cases_zero]
  exact distributionInstance g hr hf P h 3 (.var 2) (.var 1) (.var 0)
    (Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)))
    (by simpa only [Formula.realize,Term.realize,Fin.cases_zero,hv2] using ha)
    (by
      apply (GorbowRegistryDispatchProof.Boolean.guardCalibration g hr hf 3 (.var 1) P _).mpr
      obtain ⟨σ,hσ⟩ := (GorbowRegistryDispatchProof.Boolean.guardCalibration g hr hf 2 (.var 0) P
        (Fin.cases p (Fin.cases a Fin.elim0))).mp hp
      exact ⟨σ,by simpa only [Term.realize,Fin.cases_zero,hv1] using hσ⟩) hq

theorem successorClosure : Comparators.GorbowKnowledgeDispatch.SuccessorClosure := by
  intro g P φ ψ hφ hi
  have he := (GorbowSortedRevisionProof.exactImage g P).1
  exact (he ψ).mpr ((he (.imp φ ψ)).mp hi ((he φ).mp hφ))

theorem positiveDistribution : Comparators.GorbowKnowledgeDispatch.PositiveDistribution := by
  intro g hr hf initial k
  exact closureDistribution g hr hf _ (successorClosure g _)

theorem concreteInitial : Comparators.GorbowKnowledgeDispatch.ConcreteInitial := by
  have hm : MPClosed emptyInitial := by intro φ ψ h; exact h.elim
  have hs := fixedClauses GorbowAtomicRegistry.ground emptyInitial
  exact ⟨hm,fun _ h => h,hs.1,hs.2.1,hs.2.2,
    closureDistribution GorbowAtomicRegistry.ground
      GorbowAtomicRegistryProof.originalDispatch.1 GorbowAtomicRegistryProof.originalDispatch.2 _ hm⟩

theorem concreteAllStages : Comparators.GorbowKnowledgeDispatch.ConcreteAllStages := by
  intro k
  have hs := fixedClauses GorbowAtomicRegistry.ground (extensions GorbowAtomicRegistry.ground emptyInitial k)
  refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
  cases k with
  | zero => exact concreteInitial.2.2.2.2.2
  | succ k =>
    exact positiveDistribution GorbowAtomicRegistry.ground
      GorbowAtomicRegistryProof.originalDispatch.1 GorbowAtomicRegistryProof.originalDispatch.2 emptyInitial k

theorem gorbowKnowledgeDispatch : Comparators.GorbowKnowledgeDispatch.Target :=
  ⟨fixedClauses,closureDistribution,successorClosure,positiveDistribution,concreteInitial,concreteAllStages⟩
end LogicLineages.ComputabilityKnowledge.GorbowKnowledgeDispatchProof
