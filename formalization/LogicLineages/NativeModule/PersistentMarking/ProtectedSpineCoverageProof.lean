module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineLawTargets
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorSourceTupleProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineCoverageProof
open Spine DecisionInventory TypeSupport HereditaryDomainCode ProtectedSpineLaws

theorem lambdaBody (E : Environment) (H : List Head) (σ : Ty) (q : Expr)
    (h : Covered E H (.lam σ q)) : Covered E H q :=
  ⟨fun τ ht => h.1 τ (List.mem_append_right _ ht),h.2⟩

theorem lambdaType (E : Environment) (H : List Head) (σ : Ty) (q : Expr)
    (h : Covered E H (.lam σ q)) : σ ∈ E.types :=
  h.1 σ (List.mem_append_left _ (List.mem_append_right _ (DecisionSourceBasicProof.subtypeSelf σ)))

theorem ordinaryBase (E : Environment) (H : List Head) (f : Head) (bs : Args)
    (h : Covered E H (.head f bs)) : ArgsCovered E H bs :=
  ⟨fun τ ht => h.1 τ (List.mem_append_right _ ht),
    fun g hg => h.2 g (List.mem_cons_of_mem _ hg)⟩

theorem markedBase (E : Environment) (H : List Head) (f : Head) (σ : Ty) (bs es : Args)
    (h : Covered E H (.marked f σ bs es)) : ArgsCovered E H bs :=
  ⟨fun τ ht => h.1 τ (List.mem_append_left _ (List.mem_append_right _ ht)),
    fun g hg => h.2 g (List.mem_cons_of_mem _ (List.mem_append_left _ hg))⟩

theorem markedExtras (E : Environment) (H : List Head) (f : Head) (σ : Ty) (bs es : Args)
    (h : Covered E H (.marked f σ bs es)) : ArgsCovered E H es :=
  ⟨fun τ ht => h.1 τ (List.mem_append_right _ ht),
    fun g hg => h.2 g (List.mem_cons_of_mem _ (List.mem_append_right _ hg))⟩

theorem argumentCons (E : Environment) (H : List Head) (q : Expr) (qs : Args)
    (h : ArgsCovered E H (.cons q qs)) : Covered E H q ∧ ArgsCovered E H qs :=
  ⟨⟨fun τ ht => h.1 τ (List.mem_append_left _ ht),
    fun f hf => h.2 f (List.mem_append_left _ hf)⟩,
    ⟨fun τ ht => h.1 τ (List.mem_append_right _ ht),
      fun f hf => h.2 f (List.mem_append_right _ hf)⟩⟩

theorem argumentTypes (E : Environment) (H : List Head) (qs : Args)
    (h : ArgsCovered E H qs) (τ : Ty) (ht : τ ∈ (MarkedConstructorTests.terms qs).map Expr.type) :
    τ ∈ E.types := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
  exact h.1 q.type (MarkedConstructorSourceTupleProof.argumentSupport qs q hq)

end LogicLineages.PersistentMarking.ProtectedSpineCoverageProof
