module
public import LogicLineages.PermittedControl.ActualSyntaxLinearTerminalTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSyntaxLinearTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualZeroClassReplacement (Read)
open ActualLinearExit (lowerReads table exitRow)

private theorem lowerExact (top : Nat) (xs : List Read) :
    lower top (xs.map Prod.fst) = (lowerReads top xs).map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
      have tail := ih
      simp only [lower,lowerReads] at tail
      by_cases below : r.1.2.rank < top <;>
        simp [lower,lowerReads,below,tail]

private theorem slopeExact (top : Nat) (xs : List Read) :
    slope top (xs.map Prod.fst) = ActualLinearExit.slope top xs := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons,slope,ActualLinearExit.slope,ih]

private theorem namesExact (name : Nat) (xs : List Read) :
    names name (xs.map Prod.fst) = ActualLinearExit.namedTerms name xs := by
  induction xs generalizing name with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons,names,ActualLinearExit.namedTerms,ih]

theorem exactSyntaxOfLinearExit : ExactSyntaxOfLinearExit := by
  intro top constant xs
  refine ⟨lowerExact top xs,?_,?_⟩
  · simp only [termsTable,lowerExact,table,List.map_map,Function.comp_def]
  · simp only [termsRow,exitRow,slopeExact,lowerExact,namesExact]

end LogicLineages.PermittedControl.ActualSyntaxLinearTerminal
