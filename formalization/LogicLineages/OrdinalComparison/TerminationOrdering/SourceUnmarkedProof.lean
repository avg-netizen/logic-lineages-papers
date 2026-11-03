module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparisonTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceUnmarkedProof
open Source Source.SourceMarkedSyntax SourceUnmarked

private theorem groundArgumentsUnmarked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (f : Fin n → MarkedTerm Symbol arity Gamma .ground)
    (h : ∀ i,Unmarked Symbol arity Gamma (f i)) :
    ArgumentsUnmarked Symbol arity Gamma (groundArguments n f) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons _ _ (h 0) (ih (fun i => f i.succ) (fun i => h i.succ))

theorem ordinaryEmbedding : SourceExtendedComparisonTargets.OrdinaryEmbedding := by
  intro Symbol arity Gamma tau t
  induction t with
  | var v => exact .var v
  | app f a ihf iha => exact .ordinary (.application _ _) _ (.cons _ _ ihf (.cons _ _ iha .nil))
  | lam body ih => exact .lam _ ih
  | zeroC => exact .ordinary .zero .nil .nil
  | succC => exact .ordinary .succ .nil .nil
  | caseC tau => exact .ordinary (.cases tau) .nil .nil
  | recC tau => exact .ordinary (.recursor tau) .nil .nil
  | ranked f args ih => exact .ordinary (.ranked f) _ (groundArgumentsUnmarked (arity f) _ ih)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceUnmarkedProof
