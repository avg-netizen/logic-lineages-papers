module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverseTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverseProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedFiniteUniverse

theorem subtypeSelf (tau : Ty) : tau∈tau.subtypes := by
  cases tau <;> simp [Ty.subtypes]

theorem headWindow : NumberedFiniteUniverseTargets.ActualHeadWindow := by
  intro Symbol inst arity symbols S hc f
  letI := inst
  simp only [NumberedFiniteUniverse.headWindow,List.mem_filter,decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hf
    refine ⟨?_,hf⟩
    cases f with
    | zero => simp [rawHeadWindow]
    | succ => simp [rawHeadWindow]
    | cases tau =>
      have ht : tau∈S := hc (Ty.caseType tau) hf.2.1 tau (by simp [Ty.caseType,Ty.subtypes,subtypeSelf])
      simp [rawHeadWindow,ht]
    | recursor tau =>
      have ht : tau∈S := hc (Ty.recType tau) hf.2.1 tau (by simp [Ty.recType,Ty.subtypes,subtypeSelf])
      simp [rawHeadWindow,ht]
    | application sigma tau =>
      have hs : sigma∈S := hf.2.2 sigma (by simp [headArguments])
      have ht : tau∈S := hf.2.1
      simp [rawHeadWindow,hs,ht]
    | ranked s =>
      have hs : s∈symbols := hf.1
      simp [rawHeadWindow,hs]

theorem representationConfinement : NumberedFiniteUniverseTargets.ActualRepresentationConfinement := by
  intro Symbol arity K H n Gamma tau q Q h
  induction h using Represents.rec
    (motive_2 := fun Gamma types args values _ =>
      (argumentTypesAllowed K args ↔ auxArgumentTypesAllowed K values) ∧
      (argumentsAllowed H args ↔ auxArgumentsAllowed H values))
  case var => exact ⟨Iff.rfl,Iff.rfl⟩
  case lam q Q h ih => exact ⟨and_congr Iff.rfl (and_congr Iff.rfl ih.1),ih.2⟩
  case ordinary f base values h ih => exact ⟨and_congr Iff.rfl ih.1,and_congr Iff.rfl ih.2⟩
  case numbered f output base values types extras extraValues k hk hb he ihb ihe =>
    exact ⟨and_congr Iff.rfl (and_congr ihb.1 ihe.1),and_congr Iff.rfl (and_congr ihb.2 ihe.2)⟩
  case nil => exact ⟨Iff.rfl,Iff.rfl⟩
  case cons q Q rest values hq hr ihq ihr => exact ⟨and_congr ihq.1 ihr.1,and_congr ihq.2 ihr.2⟩

theorem argumentConfinement : NumberedFiniteUniverseTargets.ActualArgumentConfinement := by
  intro Symbol arity K H n Gamma types args values h
  induction types with
  | nil => cases h; exact ⟨Iff.rfl,Iff.rfl⟩
  | cons sigma types ih => cases h with
    | cons q Q rest values hq hr =>
      have ht := representationConfinement Symbol arity K H n Gamma sigma q Q hq
      have hrest := ih rest values hr
      exact ⟨and_congr ht.1 hrest.1,and_congr ht.2 hrest.2⟩

theorem sourceArgumentRootTypes {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (K : Ty → Prop) (args : Arguments Symbol arity Gamma types) (h : argumentTypesAllowed K args) : ∀ tau∈types,K tau := by
  induction types with
  | nil => intro tau ht; cases ht
  | cons sigma types ih => cases args with
    | cons q rest =>
      intro tau ht
      rcases List.mem_cons.mp ht with he | hr
      · subst tau; exact FiniteQueryPrimitivesSupportProof.rootType q h.1
      · exact ih rest h.2 tau hr

theorem unmarkedHeadWindow : NumberedFiniteUniverseTargets.ActualUnmarkedHeadWindow := by
  intro Symbol arity symbols S Gamma tau q hu ht hh
  refine SourceUnmarked.Unmarked.rec
    (motive_1 := fun Gamma tau q _ => typesAllowed (fun t => t∈S) q →
      headsAllowed (RankedCovered symbols) q → headsAllowed (HeadInWindow arity symbols S) q)
    (motive_2 := fun Gamma types args _ => argumentTypesAllowed (fun t => t∈S) args →
      argumentsAllowed (RankedCovered symbols) args → argumentsAllowed (HeadInWindow arity symbols S) args)
    ?_ ?_ ?_ ?_ ?_ hu ht hh
  · intro Gamma tau v ht hh
    trivial
  · intro Gamma sigma tau body hbody ih ht hh
    exact ih ht.2.2 hh
  · intro Gamma f base hbase ih ht hh
    exact ⟨⟨hh.1,ht.1,sourceArgumentRootTypes (fun t => t∈S) base ht.2⟩,ih ht.2 hh.2⟩
  · intro Gamma ht hh
    trivial
  · intro Gamma sigma types q rest hq hr ihq ihr ht hh
    exact ⟨ihq ht.1 hh.1,ihr ht.2 hh.2⟩

theorem unmarkedUniverse : NumberedFiniteUniverseTargets.ActualUnmarkedUniverse := by
  intro Symbol arity symbols S n Gamma tau q Q hu ht hh hQ
  have hw := unmarkedHeadWindow Symbol arity symbols S Gamma tau q hu ht hh
  have hc := representationConfinement Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S) n Gamma tau q Q hQ
  exact ⟨hc.1.mp ht,hc.2.mp hw⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverseProof
