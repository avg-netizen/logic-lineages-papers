module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutProof
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality
open PredictionBinarySentinel PredictionBinaryOutputLayout PredictionBinaryOutputLayoutTargets

private theorem relation_functional {s : TM2.Cfg StackAlphabet Λ' Store}
    {x y : TM1.Cfg TapeAlphabet TapeLabel Store}
    (hx : TM2to1.TrCfg s x) (hy : TM2to1.TrCfg s y) : x = y := by
  cases hx with
  | mk L hL =>
    cases hy with
    | mk R hR =>
      have hLR : L = R := by
        apply ListBlank.ext
        intro n
        funext k
        have h := congrArg (fun t => t.nth n) ((hL k).trans (hR k).symm)
        simpa only [proj_map_nth] using h
      cases hLR
      rfl

private def track (g : Γ') : K' → Store := slots (some g) none none none

private theorem blank_one : ListBlank.mk [(none : Store)] = ListBlank.mk [] := by
  apply ListBlank.ext
  intro n
  cases n <;> rfl

private theorem blank_two : ListBlank.mk [none, (none : Store)] = ListBlank.mk [] := by
  apply ListBlank.ext
  intro n
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

private theorem canonical_relation (b : Bool) :
    TM2to1.TrCfg (PartrecToTM2.halt [b.toNat]) (outputConfig b) := by
  cases b with
  | false =>
    apply TM2to1.TrCfg.mk (ListBlank.mk [track Γ'.cons])
    intro k
    cases k <;> simp [track, slots, halt, K'.elim, trList, trNat, trNum,
      ListBlank.map_mk, proj, blank_one, blank_two]
  | true =>
    apply TM2to1.TrCfg.mk (ListBlank.mk [track Γ'.cons, track Γ'.bit1])
    intro k
    cases k <;> simp [track, slots, halt, K'.elim, trList, trNat, trNum, trPosNum,
      ListBlank.map_mk, proj, blank_one, blank_two]

theorem exactHaltLayout : ExactHaltLayout := by
  intro b x
  constructor
  · intro h
    exact relation_functional h (canonical_relation b)
  · rintro rfl
    exact canonical_relation b

theorem exactOutputCell : ExactOutputCell := by
  intro b x hx
  have h := (exactHaltLayout b x).1 hx
  rw [h]
  cases b <;> simp [outputConfig, outputTape, Tape.mk₁, Tape.mk₂]

theorem actualPostHalt : ActualPostHalt := by
  intro b x hx
  have h := (exactHaltLayout b x).1 hx
  rw [h]
  rfl

end LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutProof
