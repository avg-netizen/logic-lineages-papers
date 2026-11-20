module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLeastTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLeastProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalCalculusSupportProof
open PositiveArithmeticOperators PositiveArithmeticLeastSetSupportProof
open NumberedWindowInternalLeastTargets

private theorem oneCoordinate (n : Nat) : (fun _ : Fin 1 => n) = ![n] := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem interpretation : ExactLeastInterpretation := by
  intro body x
  constructor
  · intro hx P hP
    have minimal := leastness (PositiveArithmeticTransforms.relabel (fun _ => (1 : Fin 2)) body)
      0 {n | P n} (fun n hn => hP n (by
        have h := (closedBodyTruth body P n).mp hn
        rwa [oneCoordinate n] at h))
    exact minimal hx
  · intro hx
    apply hx (standardLeastPredicate body)
    intro n hn
    apply (standardUnfolding body n).mpr
    rwa [oneCoordinate n]

theorem transport : ExactLeastTransport := by
  intro body F agrees x
  rw [interpretation body x]
  apply forall_congr'
  intro P
  exact imp_congr (forall_congr' fun n => imp_congr (agrees P n) Iff.rfl) Iff.rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalLeastProof
