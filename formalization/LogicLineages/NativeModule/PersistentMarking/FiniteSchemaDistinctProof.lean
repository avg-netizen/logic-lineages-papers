module

public import LogicLineages.NativeModule.PersistentMarking.FiniteSchemaExactProof

@[expose] public section

namespace LogicLineages.PersistentMarking.FiniteSchemaDistinctProof
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema

abbrev appKeys (σ : Ty) (lower : LowerCarrier σ) (Δ : Context) : List Key :=
  (fullPrefixes σ).attach.flatMap (fun p =>
    (vectors (argumentBounds σ lower Δ p.val.1 p.val.2 p.property)).map
      (fun tuple => ⟨Δ,.application p.val.1 p.val.2 tuple⟩))

theorem appMem (σ : Ty) (lower : LowerCarrier σ) (Δ : Context) (key : Key)
    (h : key ∈ appKeys σ lower Δ) :
    ∃ ds τ tuple, key = ⟨Δ,.application ds τ tuple⟩ := by
  obtain ⟨p,hp,hk⟩ := List.mem_flatMap.mp h
  obtain ⟨tuple,ht,he⟩ := List.mem_map.mp hk
  exact ⟨p.val.1,p.val.2,tuple,he.symm⟩

theorem appDistinct (σ : Ty) (lower : LowerCarrier σ) (Δ : Context) :
    (appKeys σ lower Δ).Pairwise (· ≠ ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p hp
    refine List.Pairwise.map _ ?_ (FiniteVectorProof.distinct _)
    intro a b hab he
    exact hab (Kind.application.inj (Key.mk.inj he).2).2.2
  · have hp : (fullPrefixes σ).attach.Pairwise (fun p q => p.val ≠ q.val) := by
      apply List.pairwise_map.mp
      rw [List.attach_map_subtype_val]
      exact FinitePrefixProof.distinct σ
    apply hp.imp
    intro p q hpq a ha b hb he
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp ha
    obtain ⟨ys,hys,rfl⟩ := List.mem_map.mp hb
    have hh := Kind.application.inj (Key.mk.inj he).2
    exact hpq (Prod.ext hh.1 hh.2.1)

theorem weakDistinct (Δ : Context) (obs : List Expr) (h : obs.Pairwise (· ≠ ·)) :
    (obs.map (fun t => (⟨Δ,.weak t⟩ : Key))).Pairwise (· ≠ ·) :=
  List.Pairwise.map _ (fun _ _ hn he => hn (Kind.weak.inj (Key.mk.inj he).2)) h

theorem strictDistinct (Δ : Context) (obs : List Expr) (h : obs.Pairwise (· ≠ ·)) :
    (obs.map (fun t => (⟨Δ,.strict t⟩ : Key))).Pairwise (· ≠ ·) :=
  List.Pairwise.map _ (fun _ _ hn he => hn (Kind.strict.inj (Key.mk.inj he).2)) h

theorem localDistinct (σ : Ty) (lower : LowerCarrier σ) (V : List Name) (B : Nat)
    (target : Expr) (Δ : Context) :
    ((atContext σ lower V B target Δ).map Prod.fst).Pairwise (· ≠ ·) := by
  let obs := distinctObservations (observations V B Δ target σ)
  simp only [atContext,List.map_append,List.map_cons,List.map_nil,List.map_map,List.map_flatMap]
  change (([(⟨Δ,.available⟩ : Key)] ++ obs.map (fun t => (⟨Δ,.weak t⟩ : Key)) ++
    obs.map (fun t => (⟨Δ,.strict t⟩ : Key))) ++ appKeys σ lower Δ).Pairwise (· ≠ ·)
  have ho : obs.Pairwise (· ≠ ·) := (FiniteEqualityProof.observations _).2
  apply List.pairwise_append.mpr
  refine ⟨?_,appDistinct σ lower Δ,?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨?_,strictDistinct Δ obs ho,?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨.cons (by simp) .nil,weakDistinct Δ obs ho,?_⟩
      intro a ha b hb he
      have ha : a = ⟨Δ,.available⟩ := by simpa using ha
      obtain ⟨t,ht,hb⟩ := List.mem_map.mp hb
      have hh := (Key.mk.inj (ha.symm.trans (he.trans hb.symm))).2
      cases hh
    · intro a ha b hb he
      obtain ⟨t,ht,hb⟩ := List.mem_map.mp hb
      rcases List.mem_append.mp ha with ha|ha
      · have ha : a = ⟨Δ,.available⟩ := by simpa using ha
        have hh := (Key.mk.inj (ha.symm.trans (he.trans hb.symm))).2
        cases hh
      · obtain ⟨r,hr,ha⟩ := List.mem_map.mp ha
        have hh := (Key.mk.inj (ha.trans (he.trans hb.symm))).2
        cases hh
  · intro a ha b hb he
    obtain ⟨ds,τ,tuple,hb⟩ := appMem σ lower Δ b hb
    rcases List.mem_append.mp ha with ha|ha
    · rcases List.mem_append.mp ha with ha|ha
      · have ha : a = ⟨Δ,.available⟩ := by simpa using ha
        have hh := (Key.mk.inj (ha.symm.trans (he.trans hb))).2
        cases hh
      · obtain ⟨r,hr,ha⟩ := List.mem_map.mp ha
        have hh := (Key.mk.inj (ha.trans (he.trans hb))).2
        cases hh
    · obtain ⟨r,hr,ha⟩ := List.mem_map.mp ha
      have hh := (Key.mk.inj (ha.trans (he.trans hb))).2
      cases hh

theorem full : FiniteDomainSchemaTargets.SchemaKeysDistinct := by
  intro σ lower K V B target Γ
  simp only [schema,List.map_flatMap]
  apply List.pairwise_flatMap.mpr
  refine ⟨fun Δ _ => localDistinct σ lower V B target Δ,?_⟩
  apply (FiniteExtensionProof.distinct K B Γ).imp
  intro Δ Θ hne a ha b hb he
  obtain ⟨⟨ka,ba⟩,ha,hka⟩ := List.mem_map.mp ha
  obtain ⟨⟨kb,bb⟩,hb,hkb⟩ := List.mem_map.mp hb
  have hctxa := ((FiniteSchemaExactProof.localExact σ lower V B target Δ ka ba).mp ha).1
  have hctxb := ((FiniteSchemaExactProof.localExact σ lower V B target Θ kb bb).mp hb).1
  have heq : ka = kb := hka.trans (he.trans hkb.symm)
  exact hne (hctxa.symm.trans ((congrArg Key.context heq).trans hctxb))
end LogicLineages.PersistentMarking.FiniteSchemaDistinctProof
