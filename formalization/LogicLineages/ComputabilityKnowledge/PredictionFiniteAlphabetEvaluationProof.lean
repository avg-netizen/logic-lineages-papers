module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluationTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluation
open Turing PredictionFiniteAlphabet PredictionFiniteAlphabetProof StateTransition Relation

theorem evaluationTransport : Targets.EvaluationTransport := by
  intro p c
  apply StateTransition.tr_eval' (step p) (TM0.step (machine p)) (toCfg p)
  apply StateTransition.fun_respects.mpr
  intro a
  have h := exactSingleStep p a
  cases hs : step p a with
  | none =>
    change TM0.step (machine p) (toCfg p a) = none
    simpa [hs] using h.symm
  | some d =>
    change Reaches₁ (TM0.step (machine p)) (toCfg p a) (toCfg p d)
    apply TransGen.single
    change TM0.step (machine p) (toCfg p a) = some (toCfg p d)
    simpa [hs] using h.symm

private theorem run_reaches {p : Table} {c d : Raw} {n : Nat} (h : Run p c d n) :
    Reaches (step p) c d := by
  induction h with
  | refl => exact ReflTransGen.refl
  | next hs hr ih => exact ReflTransGen.head hs ih

private theorem reaches_run {p : Table} {c d : Raw} (h : Reaches (step p) c d) :
    ∃ n, Run p c d n := by
  apply ReflTransGen.head_induction_on (motive := fun c _ => ∃ n, Run p c d n) h
  · exact ⟨0, Run.refl d⟩
  · intro a b hs hr ih
    obtain ⟨n, hn⟩ := ih
    exact ⟨n+1, Run.next hs hn⟩

private theorem raw_bounded_eval (p : Table) (c d : Raw) :
    (∃ fuel, bounded p fuel c = some d) ↔ d ∈ StateTransition.eval (step p) c := by
  constructor
  · rintro ⟨fuel, h⟩
    obtain ⟨n, hn, hr, hnone⟩ := (exactBoundedSimulation p fuel c d).mp h
    exact StateTransition.mem_eval.mpr ⟨run_reaches hr, hnone⟩
  · intro h
    obtain ⟨hr, hnone⟩ := StateTransition.mem_eval.mp h
    obtain ⟨n, hn⟩ := reaches_run hr
    exact ⟨n+1, (exactBoundedSimulation p (n+1) c d).mpr ⟨n, by omega, hn, hnone⟩⟩

theorem boundedEvaluation : Targets.BoundedEvaluation := by
  intro p c y
  rw [evaluationTransport p c]
  constructor
  · rintro ⟨fuel, d, h, heq⟩
    exact (Part.mem_map_iff (toCfg p)).mpr ⟨d, (raw_bounded_eval p c d).mp ⟨fuel,h⟩, heq⟩
  · intro h
    obtain ⟨d, hd, heq⟩ := (Part.mem_map_iff (toCfg p)).mp h
    obtain ⟨fuel, hf⟩ := (raw_bounded_eval p c d).mpr hd
    exact ⟨fuel, d, hf, heq⟩

theorem headModulo : Targets.HeadModulo := by
  intro p c
  rfl

theorem binaryOutputEvaluation : Targets.BinaryOutputEvaluation := by
  intro code xs b
  constructor
  · rintro ⟨fuel, d, hs, hb⟩
    refine ⟨toCfg (decodeTable code) d, ?_, ?_⟩
    · exact (boundedEvaluation (decodeTable code) (initial (decodeTable code) xs) _).mp
        ⟨fuel,d,hs,rfl⟩
    · exact hb
  · rintro ⟨y, hy, hb⟩
    obtain ⟨fuel,d,hs,heq⟩ :=
      (boundedEvaluation (decodeTable code) (initial (decodeTable code) xs) y).mpr hy
    refine ⟨fuel,d,hs,?_⟩
    have hh := congrArg (fun z : Cfg (decodeTable code) => z.Tape.head.val) heq
    exact hh.trans hb
end LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetEvaluation
