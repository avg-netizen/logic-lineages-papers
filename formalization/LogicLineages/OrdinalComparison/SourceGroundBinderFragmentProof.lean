module
public import LogicLineages.OrdinalComparison.SourceGroundBinderFragmentTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment.Proof
open SourceCollisionCompletion SourceAggregateCompletion PrimitiveLowering

theorem exactRenaming : Targets.ExactRenaming := by
  intro Γ Δ τ r t
  induction t generalizing Δ with
  | var x => rfl
  | app f a ihf iha => exact and_congr (ihf Δ r) (iha Δ r)
  | lam t ih => exact and_congr Iff.rfl (ih _ (Renaming.lift r))
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked s args ih => exact nomatch s

theorem eraser_fragment {Γ} (p q : OriginalTerm Γ .ground)
    (hp : Fragment p) (hq : Fragment q) : Fragment (eraser p q) := by
  exact ⟨⟨rfl,(exactRenaming _ _ _ (Renaming.weaken Γ .ground) p).mpr hp⟩,hq⟩

theorem primitiveExpressions : Targets.PrimitiveExpressions := by
  intro Γ e
  cases e with
  | port a => cases a <;> trivial
  | successor a => cases a <;> exact ⟨trivial,trivial⟩
  | erase a b =>
    apply eraser_fragment
    · cases a <;> trivial
    · cases b <;> trivial
  | identityZero => exact ⟨⟨rfl,trivial⟩,trivial⟩

theorem literalEraserDetectors : Targets.LiteralEraserDetectors := by
  intro Γ p q hp hq
  exact ⟨eraser_fragment p q hp hq,
    eraser_fragment _ _ (eraser_fragment p p hp hp) (eraser_fragment q q hq hq),
    eraser_fragment _ _ (eraser_fragment p q hp hq) (eraser_fragment q p hq hp)⟩

theorem literalAggregate : Targets.LiteralAggregate := by
  intro Γ es
  induction es with
  | nil => exact fun _ => ⟨trivial,trivial⟩
  | cons e es ih =>
    intro h
    have he := h e (List.mem_cons_self)
    have ht := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    have hd := literalEraserDetectors Γ e.1 e.2 he.1 he.2
    exact ⟨eraser_fragment _ _ hd.2.1 ht.1,eraser_fragment _ _ hd.2.2 ht.2⟩
end LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment.Proof
