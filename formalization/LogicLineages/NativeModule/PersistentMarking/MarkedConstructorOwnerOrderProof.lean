module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorLookupProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorBitOrderProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorOwnerOrderProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE)

def OwnerOrder (E : Environment) (heads : List Head) (M N : Code) (p q : Parameter) : Prop :=
  ∀ σ a, MarkedConstructorTests.owner E heads M p σ = some a →
    ∃ b, MarkedConstructorTests.owner E heads N q σ = some b ∧
      a ∈ (descriptor E σ).carriers p.2.2.1 ∧ b ∈ (descriptor E σ).carriers q.2.2.1 ∧
      (descriptor E σ).le p.2.2.1 a b = true

theorem ownerFamilyOrder (E : Environment) (heads : List Head) (M N : Code) (p : Parameter)
    (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hn : N ∈ MarkedFamilyCoherence.retained E heads) (hle : MarkedFamilyLattice.le E heads M N = true) :
    OwnerOrder E heads M N p p := by
  intro σ a ha
  let r : Parameter := (p.1, σ, p.2.2.1, p.2.2.2.1, p.2.2.2.2)
  obtain ⟨b,hb,hc,hab⟩ := MarkedConstructorLookupProof.actionOrder E heads M N r a hm hn hle ha
  exact ⟨b,hb,(MarkedConstructorLookupProof.actionValid E heads M r a ha).2,hc,hab⟩

theorem ownerInputOrder (E : Environment) (heads : List Head) (M : Code) (p q : Parameter)
    (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hq : MarkedFamilyParameters.Valid E heads q) (hpq : InputLE E p q) :
    OwnerOrder E heads M M p q := by
  intro σ a ha
  let r : Parameter := (p.1, σ, p.2.2.1, p.2.2.2.1, p.2.2.2.2)
  let s : Parameter := (q.1, σ, q.2.2.1, q.2.2.2.1, q.2.2.2.2)
  have hr := MarkedConstructorLookupProof.actionValid E heads M r a ha
  have hs : MarkedFamilyParameters.Valid E heads s := ⟨hq.1,hr.1.2.1,hq.2.2⟩
  have hrs : InputLE E r s := ⟨hpq.1,rfl,hpq.2.2⟩
  obtain ⟨b,hb,hc,hab⟩ := MarkedConstructorLookupProof.actionInputOrder E heads M r s a hm hs hrs ha
  exact ⟨b,hb,hr.2,hc,hab⟩

theorem tupleOrder (E : Environment) (heads : List Head) (M N : Code) (p q : Parameter)
    (horder : OwnerOrder E heads M N p q) (ds : List Ty) (xs : List Code)
    (hx : MarkedConstructorTests.ownerTuple E heads M p ds = some xs) :
    ∃ ys, MarkedConstructorTests.ownerTuple E heads N q ds = some ys ∧
      TupleValues E p.2.2.1 ds xs ∧ TupleValues E q.2.2.1 ds ys ∧
      ValuesLE E p.2.2.1 ds xs ys := by
  induction ds generalizing xs with
  | nil =>
    have hnil : xs = [] := (Option.some.inj hx).symm
    subst xs
    exact ⟨[],rfl,HereditaryTupleProof.tupleNil E _,HereditaryTupleProof.tupleNil E _,
      fun i σ a b h _ _ => by cases i <;> cases h⟩
  | cons σ ds ih =>
    cases ha : MarkedConstructorTests.owner E heads M p σ with
    | none => simp [MarkedConstructorTests.ownerTuple,List.mapM_cons,ha] at hx
    | some a =>
      cases has : MarkedConstructorTests.ownerTuple E heads M p ds with
      | none =>
        change ds.mapM (MarkedConstructorTests.owner E heads M p) = none at has
        simp [MarkedConstructorTests.ownerTuple,List.mapM_cons,ha,has] at hx
      | some as =>
        have hcons : a :: as = xs := by
          change ds.mapM (MarkedConstructorTests.owner E heads M p) = some as at has
          simpa [MarkedConstructorTests.ownerTuple,List.mapM_cons,ha,has] using hx
        subst xs
        obtain ⟨b,hb,hav,hbv,hle⟩ := horder σ a ha
        obtain ⟨bs,hbs,hasv,hbsv,habs⟩ := ih as has
        refine ⟨b::bs,?_,(HereditaryTupleProof.tupleCons E _ σ ds a as).mpr ⟨hav,hasv⟩,
          (HereditaryTupleProof.tupleCons E _ σ ds b bs).mpr ⟨hbv,hbsv⟩,?_⟩
        · change ds.mapM (MarkedConstructorTests.owner E heads N q) = some bs at hbs
          simp [MarkedConstructorTests.ownerTuple,List.mapM_cons,hb,hbs]
        · exact (MarkedBaseTupleFoundationProof.valuesCons E p.2.2.1 σ ds a b as bs).mpr ⟨hle,habs⟩

theorem wholeOrder (E : Environment) (heads : List Head) (M N : Code) (p q : Parameter)
    (hΓ : p.2.2.1 = q.2.2.1) (hw : WellFormed E.types E.ports p.2.2.1)
    (horder : OwnerOrder E heads M N p q) (ts : List Expr)
    (h : MarkedConstructorTargets.WholeWitness E heads M p ts) :
    MarkedConstructorTargets.WholeWitness E heads N q ts := by
  intro t ht
  obtain ⟨a,ha,hbit⟩ := h t ht
  obtain ⟨b,hb,hac,hbc,hle⟩ := horder t.type a ha
  refine ⟨b,hb,?_⟩
  rw [← hΓ] at hbc ⊢
  exact MarkedConstructorBitOrderProof.decodeMonotone false E t.type p.2.2.1 a b t hw hac hbc hle hbit

end LogicLineages.PersistentMarking.MarkedConstructorOwnerOrderProof
