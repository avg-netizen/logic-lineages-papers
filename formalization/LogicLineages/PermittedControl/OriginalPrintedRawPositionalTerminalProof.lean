module
public import LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminalTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPlainTerminalMatrix (readBits)

private theorem tapeStep (payload tag : Nat) (ht : tag < 6) :
    tape (6 * payload + tag) =
      if tag ≤ 2 then [tag]
      else if tag = 3 then tape payload ++ [3]
      else tape payload.unpair.1 ++ tape payload.unpair.2 ++ [tag] := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [tape,hm,hd]

private theorem tapeLiteral (p : NormalForm.Formula) : tape p.encode = typedTape p := by
  induction p with
  | truth => simpa [NormalForm.Formula.encode,typedTape] using tapeStep 0 0 (by decide)
  | falsity => simpa [NormalForm.Formula.encode,typedTape] using tapeStep 0 1 (by decide)
  | atom a => simpa [NormalForm.Formula.encode,typedTape] using tapeStep (Encodable.encode a.data) 2 (by decide)
  | negative p ih => simpa [NormalForm.Formula.encode,typedTape,ih] using tapeStep p.encode 3 (by decide)
  | conjunction p q ihp ihq =>
    simpa [NormalForm.Formula.encode,typedTape,Nat.unpair_pair,ihp,ihq] using
      tapeStep (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q ihp ihq =>
    simpa [NormalForm.Formula.encode,typedTape,Nat.unpair_pair,ihp,ihq] using
      tapeStep (Nat.pair p.encode q.encode) 5 (by decide)

private theorem atomCount (p : NormalForm.Formula) :
    (typedTape p).count 2 = (LinearRows.atoms p).length := by
  induction p <;> simp_all [typedTape,LinearRows.atoms,List.count_append]

theorem exactOriginalPositionalTape : ExactOriginalPositionalTape :=
  ⟨tapeLiteral,atomCount⟩

private theorem runAppend (a b : Tape) (state : Option State) :
    run (a ++ b) state = run b (run a state) := by
  exact List.foldl_append

private theorem runSingle (tag : Nat) (state : Option State) :
    run [tag] state = step state tag := rfl

private theorem runNone (t : Tape) : run t none = none := by
  induction t with
  | nil => rfl
  | cons a as ih =>
    change run as none = none
    exact ih

private theorem pushResult (p : NormalForm.Formula) (s : Stack) (bits : List Bool) :
    run (typedTape p) (some (s,bits)) =
      (readBits p bits).map (fun val => (val.1 :: s,val.2)) := by
  induction p generalizing s bits with
  | truth => rfl
  | falsity => rfl
  | atom a => cases bits <;> simp [typedTape,runSingle,step,localStep,readBits]
  | negative p ih =>
    simp only [typedTape,runAppend,runSingle,ih]
    cases hp : readBits p bits with
    | none => simp [hp,readBits,step]
    | some res =>
      rcases res with ⟨b,tail⟩
      simp [hp,readBits,step,localStep]
  | conjunction p q ihp ihq =>
    simp only [typedTape,runAppend,runSingle,ihp]
    cases hp : readBits p bits with
    | none => simp [hp,readBits,runNone,step]
    | some res =>
      rcases res with ⟨b,mid⟩
      simp only [Option.map_some,ihq]
      cases hq : readBits q mid with
      | none => simp [hp,hq,readBits,step]
      | some res =>
        rcases res with ⟨c,rest⟩
        simp [hp,hq,readBits,step,localStep]
  | disjunction p q ihp ihq =>
    simp only [typedTape,runAppend,runSingle,ihp]
    cases hp : readBits p bits with
    | none => simp [hp,readBits,runNone,step]
    | some res =>
      rcases res with ⟨b,mid⟩
      simp only [Option.map_some,ihq]
      cases hq : readBits q mid with
      | none => simp [hp,hq,readBits,step]
      | some res =>
        rcases res with ⟨c,rest⟩
        simp [hp,hq,readBits,step,localStep]

theorem exactOriginalRawPositionalRead : ExactOriginalRawPositionalRead := by
  intro p bits
  rw [readCode,tapeLiteral,pushResult]
  cases h : readBits p bits with
  | none => rfl
  | some r =>
    cases r
    rfl

theorem exactOriginalRawPositionalFinish : ExactOriginalRawPositionalFinish := by
  intro p bits polarity
  rw [finishCode,exactOriginalRawPositionalRead p bits]
  cases h : readBits p bits with
  | none => simp
  | some r =>
    rcases r with ⟨answer,tail⟩
    cases tail <;> simp [complete]

end LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminal
