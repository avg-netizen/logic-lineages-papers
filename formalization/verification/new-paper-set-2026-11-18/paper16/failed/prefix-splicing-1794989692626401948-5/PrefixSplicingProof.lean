import LogicLineages.PersistentMarking.PrefixSplicingSupport
namespace LogicLineages.PersistentMarking.PrefixSplicingProof
open Spine PrefixSplicingSupport

theorem splice (S : Signature) (f : Head) (ρ τ : Ty) (base extras : Args) (q : Expr) (newer older args : Args) (w : Expr)
    (hp : PaperTerm S (.marked f ρ base extras) ρ) (ho : PrefixCopies f base extras older)
    (ha : PrefixCopies f base extras args) (hw : w.type = τ)
    (hc : applyAux (substitute older newer.length q) args newer = some w) :
    applyAux q args (newer.append older) = some w ∨
      (applyAux q args (newer.append older) = none ∧ Refines S (.marked f τ base extras) w) := by
  cases args with
  | nil =>
    apply Or.inl
    have hb := BoundBlockProof.block newer older 0 q
    simpa only [applyAux,Nat.zero_add,hb] using hc
  | cons a rest =>
    cases q with
    | free σ x => simp [substitute,applyAux] at hc
    | bound σ i =>
      by_cases hi : i < newer.length
      · simp [substitute,hi,applyAux] at hc
      · cases hv : older.get (i-newer.length) with
        | none => simp [substitute,hi,hv,applyAux] at hc
        | some v =>
          have hc' : applyAux (shift newer.length 0 v) (.cons a rest) newer = some w := by
            simpa only [substitute,hi,if_false,hv] using hc
          obtain ⟨υ,hcopy⟩ := lookupCopy ho (i-newer.length) v hv
          exact Or.inr ⟨rfl,insertedCall S f ρ τ υ base extras v hp hcopy newer a rest ha w hw hc'⟩
    | lam σ body =>
      by_cases hty : a.type = σ
      · have hc' : applyAux (substitute older (.cons a newer).length body) rest (.cons a newer) = some w := by
          simpa only [substitute,applyAux,hty,if_true,Args.length,Nat.add_comm] using hc
        cases ha with
        | cons _ hrest =>
          have hh := splice S f ρ τ base extras body (.cons a newer) older rest w hp ho hrest hw hc'
          simpa only [applyAux,hty,if_true,Args.append] using hh
      · simp [substitute,applyAux,hty] at hc
    | head g bs =>
      apply Or.inl
      cases ht : consumeTypes g.result (.cons a rest) with
      | none => simp [substitute,applyAux,ht] at hc
      | some υ =>
        have hb := BoundBlockProof.blockArgs newer older 0 bs
        simpa only [substitute,applyAux,ht,Option.map_some,Nat.zero_add,hb] using hc
    | marked g σ bs es =>
      apply Or.inl
      cases ht : consumeTypes σ (.cons a rest) with
      | none => simp [substitute,applyAux,ht] at hc
      | some υ =>
        have hb := BoundBlockProof.blockArgs newer older 0 bs
        have he := BoundBlockProof.blockArgs newer older 0 es
        simpa only [substitute,applyAux,ht,Option.map_some,Nat.zero_add,hb,he] using hc
termination_by sizeOf args

theorem splicing : PrefixEscapeSupportTargets.Splicing := splice
end LogicLineages.PersistentMarking.PrefixSplicingProof
