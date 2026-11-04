module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCoREClassificationTargets
public import LogicLineages.OrdinalComparison.SourceGammaWeakSemidecisionProof
public import LogicLineages.OrdinalComparison.SourceBlankHaltingUniversalityProof
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCoREClassification.Proof
attribute [local irreducible] Computable Partrec Primrec SourceBlankMachineSimulation.Halts

theorem reComplement : Targets.REComplement := by
  intro b
  exact (SourceGammaWeakSemidecision.Proof.fixedSemidecision b).2.2

private theorem complement_reduction (P : Nat → Prop) (h : REPred (fun n => ¬P n)) :
    ∃ f : Nat → Nat, Primrec f ∧ ∀ n, P n ↔ nonhalting (f n) := by
  classical
  obtain ⟨⟨f,hf,he⟩,_⟩ := SourceBlankHaltingUniversality.Proof.reUniversality (fun n => ¬P n) h
  refine ⟨f,hf,?_⟩
  intro n
  change P n ↔ ¬SourceBlankMachineSimulation.Halts (f n)
  constructor
  · intro hp hh
    exact ((he n).mpr hh) hp
  · intro hn
    by_contra hp
    exact hn ((he n).mp hp)

theorem universalCoRE : Targets.UniversalCoRE := by
  intro b P h
  obtain ⟨f,hf,he⟩ := complement_reduction P h
  have first : ManyOneReducible P nonhalting := ⟨f,hf.to_comp,he⟩
  have second : ManyOneReducible nonhalting (language b) :=
    (SourceGammaWeakCodedReduction.Proof.fixedNonhaltingReduction b).2
  exact first.trans second

theorem reversePrimitiveReduction : Targets.ReversePrimitiveReduction := by
  intro b
  exact complement_reduction (language b) (reComplement b)

theorem exactManyOneEquivalence : Targets.ExactManyOneEquivalence := by
  intro b
  obtain ⟨f,hf,he⟩ := reversePrimitiveReduction b
  exact ⟨⟨f,hf.to_comp,he⟩,
    (SourceGammaWeakCodedReduction.Proof.fixedNonhaltingReduction b).2⟩
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCoREClassification.Proof
