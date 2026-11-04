module
public import LogicLineages.OrdinalComparison.ParametricSourceEraserClosureProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceEraser.Proof
open ParametricSourceSuccessor

theorem naturalObservationClosure : Targets.NaturalObservationClosure := by
  intro G hm hi Γ ρ p q x y hp hq z
  have h := (genericFiniteClosure G hm hi Γ
    (fun c => ((ρ c+1 : Nat) : Ordinal)) p q (x+1) (y+1) hp hq).2 (z+1)
  have hn : 3*(x+1)+(y+1)+4=3*x+y+8 := by omega
  rw [hn] at h
  exact h.trans (by omega)

theorem actualGammaClosure : Targets.ActualGammaClosure := by
  intro b
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  constructor
  · intro Γ ν p q x y hp hq z
    exact (genericFiniteClosure _ h.1 h.2.1 Γ ν p q x y hp hq).2 z
  · exact naturalObservationClosure _ h.1 h.2.1
end LogicLineages.OrdinalComparison.Source.ParametricSourceEraser.Proof
