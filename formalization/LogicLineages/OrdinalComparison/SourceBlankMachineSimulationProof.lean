module
public import LogicLineages.OrdinalComparison.SourceBlankMachineSimulationTargets
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankMachineSimulation.Proof
open Turing LogicLineages.ComputabilityKnowledge
open PredictionFiniteAlphabet

section
attribute [local irreducible] simulate

theorem effectiveEnumeration : Targets.EffectiveEnumeration := by
  refine ⟨PredictionFiniteAlphabetProof.effectiveDecoding.1,
    PredictionFiniteAlphabetProof.effectiveDecoding.2, ?_⟩
  have hs : Primrec (fun z : Nat × Nat => simulate z.1 (z.2+1) []) :=
    PredictionFiniteAlphabetProof.effectiveBoundedSimulation.comp
      (Primrec.fst.pair ((Primrec.nat_add.comp Primrec.snd (Primrec.const 1)).pair
        (Primrec.const ([] : List Bool))))
  apply (Primrec.not.comp ((Primrec.eq.comp hs (Primrec.const none)).decide)).of_eq
  intro z
  unfold boundedH
  cases simulate z.1 (z.2+1) [] <;> rfl

end

theorem exactTransitionClock : Targets.ExactTransitionClock := by
  intro e t
  change (bounded (program e) (t+1) (initial (program e) [])).isSome = true ↔ _
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨d,hd⟩
    obtain ⟨n,hn,hr,he⟩ := (PredictionFiniteAlphabetProof.exactBoundedSimulation
      (program e) (t+1) (initial (program e) []) d).1 hd
    exact ⟨d,n,by omega,hr,he⟩
  · rintro ⟨d,n,hn,hr,he⟩
    exact ⟨d,(PredictionFiniteAlphabetProof.exactBoundedSimulation
      (program e) (t+1) (initial (program e) []) d).2 ⟨n,by omega,hr,he⟩⟩

theorem monotoneHalting : Targets.MonotoneHalting := by
  constructor
  · intro e t u htu ht
    obtain ⟨d,n,hn,hr,he⟩ := (exactTransitionClock e t).1 ht
    exact (exactTransitionClock e u).2 ⟨d,n,hn.trans htu,hr,he⟩
  · intro e
    constructor
    · intro h
      obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp h
      obtain ⟨fuel,d,hd,_⟩ := (PredictionFiniteAlphabetEvaluation.boundedEvaluation
        (program e) (initial (program e) []) y).2 hy
      obtain ⟨n,hn,hr,he⟩ := (PredictionFiniteAlphabetProof.exactBoundedSimulation
        (program e) fuel (initial (program e) []) d).1 hd
      exact ⟨n,(exactTransitionClock e n).2 ⟨d,n,le_rfl,hr,he⟩⟩
    · rintro ⟨t,ht⟩
      obtain ⟨d,hd⟩ := Option.isSome_iff_exists.mp ht
      apply Part.dom_iff_mem.mpr
      refine ⟨toCfg (program e) d, ?_⟩
      exact (PredictionFiniteAlphabetEvaluation.boundedEvaluation
        (program e) (initial (program e) []) (toCfg (program e) d)).1
        ⟨t+1,d,hd,rfl⟩
end LogicLineages.OrdinalComparison.SourceBlankMachineSimulation.Proof
