module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedKnowledgeAxioms
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanTruthProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxiomsProof
open GorbowSyntax GorbowSortedRevision GorbowSortedSyntaxCode GorbowBooleanTruth
open GorbowSortedKnowledgeAxioms

theorem fixedClauses : Comparators.GorbowSortedKnowledgeAxioms.FixedClauses := by
  intro P
  refine ⟨?_,?_,?_⟩
  · exact ⟨0,rfl⟩
  · intro code _
    change (P code → ∀ a, a=0 → a=0 ∧ P code) ∧ ((∀ a, a=0 → a=0 ∧ P code) → P code)
    exact ⟨fun h a ha => ⟨ha,h⟩,fun h => (h 0 rfl).2⟩
  · intro a _ code _ h
    exact h.2

private theorem distributionInstance (P : Extension)
    (hP : ∀ φ ψ : Sentence, P (formulaCode φ) → P (formulaCode (.imp φ ψ)) → P (formulaCode ψ))
    (n : Nat) (a s t : Term n) ρ
    (ha : (Formula.agent a).realize (interpretation GorbowSortedRegistry.ground P) ρ)
    (hs : (sentenceGuard s).realize (interpretation GorbowSortedRegistry.ground P) ρ)
    (ht : (sentenceGuard t).realize (interpretation GorbowSortedRegistry.ground P) ρ) :
    (Formula.imp (.conj (.knowledge a s) (.knowledge a (binaryCodeTerm 0 s t)))
      (.knowledge a t)).realize (interpretation GorbowSortedRegistry.ground P) ρ := by
  obtain ⟨φ,hφ⟩ := (GorbowSortedBooleanTruthProof.guardCalibration n s P ρ).mp hs
  obtain ⟨ψ,hψ⟩ := (GorbowSortedBooleanTruthProof.guardCalibration n t P ρ).mp ht
  have hi := (GorbowSortedBooleanTruthProof.functionCalibration n s t P ρ φ ψ hφ hψ).2.1
  intro h
  change a.realize _ ρ=0 ∧ P (t.realize _ ρ)
  refine ⟨ha,?_⟩
  rw [hψ]
  apply hP φ ψ
  · simpa only [hφ] using h.1.2
  · simpa only [hi] using h.2.2

attribute [local irreducible] GorbowRegistryTuple.headerTerm GorbowRegistryTuple.pairTerm GorbowRegistryTuple.tupleTerm

theorem initialClosure : Comparators.GorbowSortedKnowledgeAxioms.InitialClosure := by
  intro P h a ha p hp q hq
  have hv2 : Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)) (2 : Fin 3)=a := by
    change Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)) (0 : Fin 1).succ.succ=a
    rw [Fin.cases_succ,Fin.cases_succ,Fin.cases_zero]
  have hv1 : Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)) (1 : Fin 3)=p := by
    change Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)) (0 : Fin 2).succ=p
    rw [Fin.cases_succ,Fin.cases_zero]
  exact distributionInstance P h 3 (.var 2) (.var 1) (.var 0)
    (Fin.cases q (Fin.cases p (Fin.cases a Fin.elim0)))
    (by simpa only [Formula.realize,Term.realize,Fin.cases_zero,hv2] using ha)
    (by
      apply (GorbowSortedBooleanTruthProof.guardCalibration 3 (.var 1) P _).mpr
      obtain ⟨σ,hσ⟩ := (GorbowSortedBooleanTruthProof.guardCalibration 2 (.var 0) P
        (Fin.cases p (Fin.cases a Fin.elim0))).mp hp
      exact ⟨σ,by simpa only [Term.realize,Fin.cases_zero,hv1] using hσ⟩) hq

theorem positiveDistribution : Comparators.GorbowSortedKnowledgeAxioms.PositiveDistribution := by
  intro initial k
  apply initialClosure
  intro φ ψ hφ hi
  have he := (GorbowSortedRevisionProof.exactImage GorbowSortedRegistry.ground
    (extensions GorbowSortedRegistry.ground initial k)).1
  exact (he ψ).mpr ((he (.imp φ ψ)).mp hi ((he φ).mp hφ))

theorem gorbowSortedKnowledgeAxioms : Comparators.GorbowSortedKnowledgeAxioms.Target :=
  ⟨fixedClauses,positiveDistribution,initialClosure⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxiomsProof
