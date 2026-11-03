module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryContextStabilityTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryContextStabilityProof
open Source Source.SourceMarkedSyntax RecursiveComparison LiteralContexts ConfinedOrdinarySubstitution

private theorem groundMatch {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (n : Nat)
    (f g : Fin n → MarkedTerm Symbol arity Gamma .ground)
    (h : ∀ i,Weak Symbol arity above Gamma ⟨.ground,f i⟩ ⟨.ground,g i⟩) :
    WeakMatch Symbol arity above Gamma (argumentList (groundArguments n f)) (argumentList (groundArguments n g)) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons _ _ _ _ (h 0) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

theorem weakContextClosure : OrdinaryContextStabilityTargets.WeakContextClosure := by
  intro Symbol arity above Delta Gamma upsilon tau C s t h
  induction C with
  | hole => exact h
  | appFunction C a ih =>
    apply Weak.fun_ (.application _ _) (.application _ _)
      (.cons (embed (plug C s)) (.cons (embed a) .nil))
      (.cons (embed (plug C t)) (.cons (embed a) .nil)) _ rfl rfl (.refl _)
    exact .cons _ _ _ _ ih (.cons _ _ _ _
      (RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above _ _ a) .nil)
  | appArgument f C ih =>
    apply Weak.fun_ (.application _ _) (.application _ _)
      (.cons (embed f) (.cons (embed (plug C s)) .nil))
      (.cons (embed f) (.cons (embed (plug C t)) .nil)) _ rfl rfl (.refl _)
    exact .cons _ _ _ _
      (RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above _ _ f)
      (.cons _ _ _ _ ih .nil)
  | lam C ih => exact .abs _ _ ih
  | ranked f i args C ih =>
    apply Weak.fun_ (.ranked f) (.ranked f)
      (groundArguments (arity f) (fun j => embed (if j=i then plug C s else args j)))
      (groundArguments (arity f) (fun j => embed (if j=i then plug C t else args j))) _ rfl rfl (.refl _)
    apply groundMatch
    intro j
    by_cases hj : j=i
    · simpa only [if_pos hj] using ih
    · simpa only [if_neg hj] using
        RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above _ _ (args j)

theorem bothConfinedContextClosure : OrdinaryContextStabilityTargets.BothConfinedContextClosure := by
  intro Symbol arity above Delta Gamma upsilon tau C s t
  constructor
  · intro h
    exact ⟨weakContextClosure Symbol arity above Delta Gamma upsilon tau C s t h.1,
      LiteralContextsProof.literalContextSupportMonotonicity Symbol arity Delta Gamma upsilon tau C s t h.2⟩
  · exact LiteralContextsProof.literalConfinedContextClosure Symbol arity above Delta Gamma upsilon tau C s t

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryContextStabilityProof
