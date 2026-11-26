module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorBitOrderProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedBaseTupleFoundationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorStatOrderProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open MarkedConstructorTargets (Matches Replaces SplitList)

/-- Each old source position has its own new source position. -/
inductive BaseOrder (E : Environment) (Γ : Context) :
    List MarkedExtras.Tagged → List MarkedExtras.Tagged → Prop where
  | nil : BaseOrder E Γ [] []
  | cons : (∀ strict t, MarkedConstructorTests.bit strict E Γ a t = true →
      MarkedConstructorTests.bit strict E Γ b t = true) →
      BaseOrder E Γ as bs → BaseOrder E Γ (a::as) (b::bs)

theorem baseOrder (E : Environment) (Γ : Context) (ds : List Ty) (xs ys : List Code)
    (hw : WellFormed E.types E.ports Γ) (hx : TupleValues E Γ ds xs)
    (hy : TupleValues E Γ ds ys) (hle : ValuesLE E Γ ds xs ys) :
    BaseOrder E Γ (ds.zip xs) (ds.zip ys) := by
  induction ds generalizing xs ys with
  | nil => exact .nil
  | cons σ ds ih =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      cases ys with
      | nil => cases hy.1
      | cons y ys =>
        have hxs := (HereditaryTupleProof.tupleCons E Γ σ ds x xs).mp hx
        have hys := (HereditaryTupleProof.tupleCons E Γ σ ds y ys).mp hy
        have hxy := (MarkedBaseTupleFoundationProof.valuesCons E Γ σ ds x y xs ys).mp hle
        have htag : MarkedExtras.le E Γ (σ,x) (σ,y) = true := by
          simpa only [MarkedExtras.le, decide_true, Bool.true_and] using hxy.1
        exact .cons (fun strict t => MarkedConstructorBitOrderProof.taggedMonotone
            strict E Γ (σ,x) (σ,y) t hw hxs.1 hys.1 htag)
          (ih xs ys hxs.2 hys.2 hxy.2)

theorem splitOrder {E Γ as bs kept removed} (hs : SplitList as kept removed)
    (hle : BaseOrder E Γ as bs) :
    ∃ kept' removed', SplitList bs kept' removed' ∧
      BaseOrder E Γ kept kept' ∧ BaseOrder E Γ removed removed' := by
  induction hs generalizing bs with
  | nil =>
    cases hle
    exact ⟨[],[],.nil,.nil,.nil⟩
  | left hs ih =>
    cases hle with
    | cons hab htail =>
      obtain ⟨ks,rs,hs',hk,hr⟩ := ih htail
      exact ⟨_,rs,.left hs',.cons hab hk,hr⟩
  | right hs ih =>
    cases hle with
    | cons hab htail =>
      obtain ⟨ks,rs,hs',hk,hr⟩ := ih htail
      exact ⟨ks,_,.right hs',hk,.cons hab hr⟩

theorem matchOrder {E Γ as bs ts} (hm : Matches E Γ as ts) (hle : BaseOrder E Γ as bs) :
    Matches E Γ bs ts := by
  induction hm generalizing bs with
  | nil =>
    cases hle
    exact .nil
  | cons hd ha htail ih =>
    cases hle with
    | cons hab hrest => exact .cons hd (hab false _ ha) (ih hrest)

theorem memberOrder {E Γ as bs} (hle : BaseOrder E Γ as bs) (a : MarkedExtras.Tagged)
    (ha : a ∈ as) : ∃ b, b ∈ bs ∧ ∀ strict t, MarkedConstructorTests.bit strict E Γ a t = true →
      MarkedConstructorTests.bit strict E Γ b t = true := by
  induction hle with
  | nil => cases ha
  | cons hab htail ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_,List.mem_cons_self,hab⟩
    · obtain ⟨b,hb,hbit⟩ := ih ha
      exact ⟨b,List.mem_cons_of_mem _ hb,hbit⟩

theorem replaceOrder {E Γ as bs ts} (h : Replaces E Γ as ts) (hle : BaseOrder E Γ as bs) :
    Replaces E Γ bs ts := by
  obtain ⟨kept,removed,matched,added,hs,ht,hn,hm,hcovers⟩ := h
  obtain ⟨ks,rs,hs',hk,hr⟩ := splitOrder hs hle
  refine ⟨ks,rs,matched,added,hs',ht,?_,matchOrder hm hk,?_⟩
  · intro hempty
    subst rs
    cases hr
    exact hn rfl
  · intro t ht
    obtain ⟨a,ha,hbit⟩ := hcovers t ht
    obtain ⟨b,hb,hab⟩ := memberOrder hr a ha
    exact ⟨b,hb,hab true t hbit⟩

end LogicLineages.PersistentMarking.MarkedConstructorStatOrderProof
