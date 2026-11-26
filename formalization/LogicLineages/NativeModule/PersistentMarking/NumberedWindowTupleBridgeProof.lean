module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSourceGuardChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowTupleBridgeProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowApplicationTargets NumberedWindowSourceGuardTargets
open DecisionInventory (auxiliarySupport auxiliaryArgs declaration)

def Conclusion (S : Signature) (K : List Ty) (C : BoundContext) (n : Nat) (τ : Ty)
    (Q : NTerm) (As : NArgs) (r : Expr) : Prop :=
  ∃ start out, applications Q As = some start ∧
    WindowPath S K C τ start out ∧ Realizes n r out

mutual
theorem emptySubstitute (Q : NTerm) (d : Nat) :
    NumberedWindowSyntax.substitute .nil d Q = Q := by
  cases Q with
  | free σ x => rfl
  | bound σ i => simp [NumberedWindowSyntax.substitute,NArgs.get,NArgs.length]
  | lam σ Q => simp only [NumberedWindowSyntax.substitute,emptySubstitute Q]
  | bottom τ => rfl
  | ordinary f bs => simp only [NumberedWindowSyntax.substitute,emptySubstituteArgs bs]
  | numbered f τ k bs es =>
    simp only [NumberedWindowSyntax.substitute,emptySubstituteArgs bs,emptySubstituteArgs es]
  | auxApp σ τ q a => simp only [NumberedWindowSyntax.substitute,emptySubstitute q,emptySubstitute a]
termination_by sizeOf Q

theorem emptySubstituteArgs (As : NArgs) (d : Nat) :
    NumberedWindowSyntax.substituteArgs .nil d As = As := by
  cases As with
  | nil => rfl
  | cons q rest => simp only [NumberedWindowSyntax.substituteArgs,emptySubstitute q,emptySubstituteArgs rest]
termination_by sizeOf As
end

theorem appendRealizes {n : Nat} (args tail : Spine.Args) (As Tail : NArgs)
    (ha : RealizesArgs n args As) (ht : RealizesArgs n tail Tail) :
    RealizesArgs n (args.append tail) (As.append Tail) := by
  cases args with
  | nil => cases ha; exact ht
  | cons a rest =>
    cases ha with
    | cons h hr => exact .cons h (appendRealizes _ tail _ Tail hr ht)
termination_by sizeOf args

theorem pushValues {S : Signature} {K : List Ty} {C : BoundContext}
    {σ : Ty} {types : List Ty} {q : Expr} {values : Spine.Args}
    (hq : SourceGuard S K C σ q) (hv : SourceValues S K C types values) :
    SourceValues S K C (σ::types) (.cons q values) := by
  refine ⟨.cons hq.1 hv.1,⟨hq.2.1,hv.2.1⟩,?_⟩
  intro ρ hρ
  simp only [auxiliaryArgs,List.mem_append] at hρ
  exact hρ.elim (hq.2.2 ρ) (hv.2.2 ρ)

theorem markWindow {S : Signature} {K : List Ty} {C : BoundContext}
    {f : Head} {bs : NArgs} (h : InWindow S K C f.result (.ordinary f bs)) (label : Nat) :
    InWindow S K C f.result (.numbered f f.result label bs .nil) := by
  have hb : NumberedWindowDomain.BaseTyped C bs f.arguments := by
    cases h.1 with
    | ordinary h => exact h
  have hf : HeadInWindow S K f := h.2.2 f List.mem_cons_self
  have hBs : NumberedWindowNumberedDomainProof.ArgsGuard S K bs :=
    ⟨fun ρ hρ => h.2.1 ρ (List.mem_append_right _ hρ),
      fun g hg => h.2.2 g (List.mem_cons_of_mem _ hg)⟩
  have hempty : NumberedWindowNumberedDomainProof.ArgsGuard S K .nil :=
    ⟨fun _ h => False.elim (List.not_mem_nil h),fun _ h => False.elim (List.not_mem_nil h)⟩
  exact NumberedWindowNumberedDomainProof.numbered hb .nil hf
    (fun ρ hρ => hf.2 ρ (List.mem_append_left _ hρ)) hBs hempty

theorem functionPrefix {S : Signature} {K : List Ty} {C : BoundContext}
    {ds : List Ty} {τ : Ty} {n : Nat} {Q R : NTerm} {As : NArgs} {r : Expr}
    (hk : DecisionSourceUniverse.Closed K)
    (hArgs : ArgsWindow S K C ds As)
    (pref : WindowPath S K C (ArrowPrefix ds τ) Q R)
    (later : Conclusion S K C n τ R As r) : Conclusion S K C n τ Q As r := by
  obtain ⟨start,mid,hStart,hMid,hPref⟩ := NumberedWindowApplicationPathProof.lift S K C ds τ Q R As hk pref hArgs
  obtain ⟨mid',out,hMid',hLater,hRealizes⟩ := later
  have hSame : mid = mid' := Option.some.inj (hMid.symm.trans hMid')
  subst mid'
  exact ⟨start,out,hStart,NumberedWindowApplicationPathProof.trans hPref hLater,hRealizes⟩

end LogicLineages.PersistentMarking.NumberedWindowTupleBridgeProof
