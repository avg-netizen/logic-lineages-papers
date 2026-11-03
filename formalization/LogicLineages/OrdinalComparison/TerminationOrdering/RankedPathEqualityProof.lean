module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEmbeddingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEqualityProof
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree RankedPathOrder

theorem equality {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Tree Symbol arity Gamma}
    (h : Equal Symbol arity Gamma s t) : RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t) := by
  induction h using Equal.rec
    (motive_2 := fun ss ts _ => WeakMatch Symbol arity above Gamma (ss.map pack) (ts.map pack)) with
  | var v => exact .var v
  | node f ss ts matched hp hm ih =>
    apply RecursiveComparison.Weak.fun_ (.ranked f) (.ranked f)
      (groundArguments (arity f) (fun i => markedSyntax (ss i)))
      (groundArguments (arity f) (fun i => markedSyntax (ts i)))
      (matched.map pack) rfl rfl
    · change (argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun i => markedSyntax (ts i)))).Perm (matched.map pack)
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts]
      exact hp.map pack
    · change WeakMatch Symbol arity above Gamma
        (argumentList (types := List.replicate (arity f) Ty.ground)
          (groundArguments (arity f) (fun i => markedSyntax (ss i)))) (matched.map pack)
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss]
      exact ih
  | nil => exact .nil
  | cons s t ss ts hq hr ihq ihr => exact .cons _ _ _ _ ihq ihr

theorem equalityMatch {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Tree Symbol arity Gamma)}
    (h : EqualMatch Symbol arity Gamma ss ts) :
    WeakMatch Symbol arity above Gamma (ss.map pack) (ts.map pack) := by
  induction h using EqualMatch.rec
    (motive_1 := fun s t _ => RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t)) with
  | var v => exact .var v
  | node f ss ts matched hp hm ih =>
    apply RecursiveComparison.Weak.fun_ (.ranked f) (.ranked f)
      (groundArguments (arity f) (fun i => markedSyntax (ss i)))
      (groundArguments (arity f) (fun i => markedSyntax (ts i)))
      (matched.map pack) rfl rfl
    · change (argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun i => markedSyntax (ts i)))).Perm (matched.map pack)
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts]
      exact hp.map pack
    · change WeakMatch Symbol arity above Gamma
        (argumentList (types := List.replicate (arity f) Ty.ground)
          (groundArguments (arity f) (fun i => markedSyntax (ss i)))) (matched.map pack)
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss]
      exact ih
  | nil => exact .nil
  | cons s t ss ts hq hr ihq ihr => exact .cons _ _ _ _ ihq ihr

theorem equalityEmbedding : RankedPathEmbeddingTargets.EqualityEmbedding := by
  intro Symbol arity Gamma above
  exact ⟨fun _ _ h => equality above h,fun _ _ h => equalityMatch above h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEqualityProof
