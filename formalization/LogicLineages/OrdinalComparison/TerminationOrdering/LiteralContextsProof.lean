module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsSupportProof
public import LogicLineages.OrdinalComparison.SourceNamedSyntaxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsProof
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison LiteralContexts

theorem strictMultisetFromStrictMatch : LiteralContextsTargets.StrictMultisetFromStrictMatch :=
  LiteralContextsSupportProof.strictMultisetFromStrictMatch
theorem actualZeroArgumentSelect : LiteralContextsTargets.ActualZeroArgumentSelect :=
  LiteralContextsSupportProof.actualZeroArgumentSelect
theorem ordinaryHeadStrictCongruence : LiteralContextsTargets.OrdinaryHeadStrictCongruence :=
  LiteralContextsSupportProof.ordinaryHeadStrictCongruence
theorem lambdaStrictCongruence : LiteralContextsTargets.LambdaStrictCongruence :=
  LiteralContextsSupportProof.lambdaStrictCongruence

private theorem groundMatch {Symbol : Type} {arity : Symbol → Nat}
    (above : Symbol → Symbol → Prop) {Γ : List Ty} (n : Nat)
    (f g : Fin n → MarkedTerm Symbol arity Γ .ground)
    (h : ∀ i,Weak Symbol arity above Γ ⟨.ground,f i⟩ ⟨.ground,g i⟩) :
    WeakMatch Symbol arity above Γ (argumentList (groundArguments n f)) (argumentList (groundArguments n g)) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons _ _ _ _ (h 0) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

private theorem groundZip {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} (n : Nat)
    (f g : Fin n → MarkedTerm Symbol arity Γ .ground) (i : Fin n) :
    (⟨.ground,f i⟩,⟨.ground,g i⟩) ∈
      (argumentList (groundArguments n f)).zip (argumentList (groundArguments n g)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (fun j => f j.succ) (fun j => g j.succ) j)

theorem literalContextStrictClosure : LiteralContextsTargets.LiteralContextStrictClosure := by
  intro Symbol arity above Δ Γ υ τ C s t h
  induction C with
  | hole => exact h
  | appFunction C a ih =>
      apply ordinaryHeadStrictCongruence Symbol arity above _ (.application _ _)
      · exact .cons _ _ _ _ (RecursiveComparisonProof.strictWeakInclusion Symbol arity above _ _ _ ih)
          (.cons _ _ _ _ (RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above _ _ a) .nil)
      · exact ⟨_,_,by simp [argumentList],ih⟩
  | appArgument f C ih =>
      apply ordinaryHeadStrictCongruence Symbol arity above _ (.application _ _)
      · exact .cons _ _ _ _ (RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above _ _ f)
          (.cons _ _ _ _ (RecursiveComparisonProof.strictWeakInclusion Symbol arity above _ _ _ ih) .nil)
      · exact ⟨_,_,by simp [argumentList],ih⟩
  | lam C ih => exact lambdaStrictCongruence Symbol arity above _ _ _ _ _ ih
  | ranked f i args C ih =>
      apply ordinaryHeadStrictCongruence Symbol arity above _ (.ranked f)
      · apply groundMatch
        intro j
        by_cases hj : j=i
        · subst j
          simpa [plug,embed] using RecursiveComparisonProof.strictWeakInclusion Symbol arity above _ _ _ ih
        · simpa [plug,embed,hj] using RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above _ _ (args j)
      · refine ⟨_,_,groundZip (arity f) _ _ i,?_⟩
        simpa [plug,embed] using ih

theorem literalContextSupportMonotonicity : LiteralContextsTargets.LiteralContextSupportMonotonicity := by
  intro Symbol arity Δ Γ υ τ C s t h
  induction C with
  | hole => exact h
  | appFunction C a ih =>
      exact Finset.union_subset_union (by rfl) (Finset.union_subset_union ih (by rfl))
  | appArgument f C ih =>
      exact Finset.union_subset_union (by rfl) (Finset.union_subset_union (by rfl) ih)
  | lam C ih => exact Finset.union_subset_union (by rfl) ih
  | ranked f i args C ih =>
      apply Finset.union_subset_union (by rfl)
      intro ρ hρ
      obtain ⟨j,hj,hmem⟩ := Finset.mem_biUnion.mp hρ
      apply Finset.mem_biUnion.mpr
      refine ⟨j,hj,?_⟩
      by_cases he : j=i
      · subst j
        simp only [if_pos rfl] at hmem ⊢
        exact ih hmem
      · simpa only [if_neg he] using hmem

theorem literalConfinedContextClosure : LiteralContextsTargets.LiteralConfinedContextClosure := by
  intro Symbol arity above Δ Γ υ τ C s t h
  exact ⟨literalContextStrictClosure Symbol arity above Δ Γ υ τ C s t h.1,
    literalContextSupportMonotonicity Symbol arity Δ Γ υ τ C s t h.2⟩

open Source.SourceNamedSyntax

theorem namedContextErasure : LiteralContextsTargets.NamedContextErasure := by
  intro Symbol arity Δ Γ υ τ C s
  induction C with
  | hole => rfl
  | appFunction C a ih => simp only [namedPlug,erase,plug,eraseContext,ih]
  | appArgument f C ih => simp only [namedPlug,erase,plug,eraseContext,ih]
  | lam x C ih => exact congrArg (fun q => Term.lam q) ih
  | ranked f i args C ih =>
      simp only [namedPlug,erase,plug,eraseContext]
      apply congrArg (Term.ranked f)
      funext j
      by_cases hj : j=i <;> simp [namedPlug,erase,plug,eraseContext,hj,ih]

theorem fullNamedContextStrictClosure : LiteralContextsTargets.FullNamedContextStrictClosure := by
  intro Symbol arity above Δ Γ υ τ C s t h
  rw [namedContextErasure Symbol arity Δ Γ υ τ C s,namedContextErasure Symbol arity Δ Γ υ τ C t]
  exact literalContextStrictClosure Symbol arity above (contextTypes Δ) (contextTypes Γ) υ τ (eraseContext C) (erase s) (erase t) h

theorem fullNamedConfinedContextClosure : LiteralContextsTargets.FullNamedConfinedContextClosure := by
  intro Symbol arity above Δ Γ υ τ C s t h
  refine ⟨fullNamedContextStrictClosure Symbol arity above Δ Γ υ τ C s t h.1,?_⟩
  have hs : typeSupport (erase t) ⊆ typeSupport (erase s) := by
    rw [SourceNamedSyntaxProof.namedSupportCalibration Symbol arity Δ υ t,
      SourceNamedSyntaxProof.namedSupportCalibration Symbol arity Δ υ s]
    exact h.2
  have hout := literalContextSupportMonotonicity Symbol arity (contextTypes Δ) (contextTypes Γ) υ τ (eraseContext C) (erase s) (erase t) hs
  rw [←namedContextErasure Symbol arity Δ Γ υ τ C s,←namedContextErasure Symbol arity Δ Γ υ τ C t] at hout
  rw [SourceNamedSyntaxProof.namedSupportCalibration Symbol arity Γ τ (namedPlug C t),
    SourceNamedSyntaxProof.namedSupportCalibration Symbol arity Γ τ (namedPlug C s)] at hout
  exact hout

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsProof
