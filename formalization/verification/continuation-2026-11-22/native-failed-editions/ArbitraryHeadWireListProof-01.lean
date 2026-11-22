module
public import LogicLineages.PermittedControl.ArbitraryHeadWireListTargets
import LogicLineages.PermittedControl.ArbitraryHeadWireListAssignmentsProof
import LogicLineages.PermittedControl.ArbitraryHeadSharedWireRawProof

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadWireList
open ArbitraryHeadSharedWire (Valuation originalGraph limitPair)

private theorem stillOriginal (f : Nat → Nat) (g : Gate) (ν θ : Valuation)
    (hs : θ g.source = ν g.source) (ho : θ g.output = ν g.output) :
    originalGraph f g.head g.source g.output θ ↔ originalGraph f g.head g.source g.output ν := by
  unfold originalGraph
  rw [hs,ho]

private theorem finiteAt (f : Nat → Nat) (g : Gate) (ν θ : Valuation) (finite : g.finite = true)
    (hs : θ g.source = ν g.source) (ho : θ g.output = ν g.output) :
    (normalizeGate g).Holds f θ ↔ originalGraph f g.head g.source g.output ν := by
  rw [normalizeGate,finite,NormalGate.Holds]
  exact (ArbitraryHeadSharedWire.exactFiniteWire f g.head finite
    g.source g.output θ).symm.trans (stillOriginal f g ν θ hs ho)

private theorem infiniteAt (f : Nat → Nat) (g : Gate) (ν θ : Valuation) (inf : g.finite = false)
    (hs : θ g.source = ν g.source) (ho : θ g.output = ν g.output)
    (freshSource : g.hidden ≠ g.source) (freshOut : g.hidden ≠ g.output) :
    (normalizeGate g).Holds f θ ↔
      originalGraph f g.head g.source g.output ν ∧ θ g.hidden = g.shift ν := by
  have h := (ArbitraryHeadSharedWire.exactInfiniteWire f g.head inf g.source g.hidden
    g.output freshSource freshOut θ).1 (θ g.hidden)
  rw [Function.update_eq_self] at h
  rw [stillOriginal f g ν θ hs ho] at h
  change limitPair f g.head g.source g.hidden g.output θ ↔
    originalGraph f g.head g.source g.output ν ∧
      θ g.hidden = (ArbitraryFixedHeadCollapse.transported
        (ArbitraryHeadSharedWire.headCode g.head,θ g.source)).2 at h
  rw [hs] at h
  simpa only [normalizeGate,inf,NormalGate.Holds] using h

private theorem normalizedIff (f : Nat → Nat) (gates : List Gate) (θ : Valuation) :
    NormalizedAt f θ gates ↔ ∀ g ∈ gates, (normalizeGate g).Holds f θ := by
  constructor
  · intro h g hg
    exact h _ (List.mem_map.mpr ⟨g,hg,rfl⟩)
  · intro h n hn
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hn
    exact h g hg

private theorem conjunction (f : Nat → Nat) (gates : List Gate) (fresh : Fresh gates)
    (ν θ : Valuation) (agree : Agrees gates ν θ) :
    NormalizedAt f θ gates ↔ OriginalAt f ν gates ∧ Prescribed gates ν θ := by
  have reads (g : Gate) (hg : g ∈ gates) :
      θ g.source = ν g.source ∧ θ g.output = ν g.output :=
    ⟨agree g.source (fresh.2 g hg).1,agree g.output (fresh.2 g hg).2⟩
  have freshWires (g : Gate) (hg : g ∈ gates) (hinf : g.finite = false) :
      g.hidden ≠ g.source ∧ g.hidden ≠ g.output := by
    have mem := hiddenMember hg hinf
    exact ⟨fun h => (fresh.2 g hg).1 (h ▸ mem),fun h => (fresh.2 g hg).2 (h ▸ mem)⟩
  rw [normalizedIff]
  constructor
  · intro all
    refine ⟨?_,?_⟩
    · intro g hg
      have hs := (reads g hg).1
      have ho := (reads g hg).2
      cases hb : g.finite with
      | true => exact (finiteAt f g ν θ hb hs ho).mp (all g hg)
      | false =>
          obtain ⟨different,other⟩ := freshWires g hg hb
          exact ((infiniteAt f g ν θ hb hs ho different other).mp (all g hg)).1
    · intro g hg inf
      obtain ⟨different,other⟩ := freshWires g hg inf
      exact ((infiniteAt f g ν θ inf ((reads g hg).1)
        ((reads g hg).2) different other).mp (all g hg)).2
  · rintro ⟨all,assigned⟩ g hg
    have hs := (reads g hg).1
    have ho := (reads g hg).2
    cases hb : g.finite with
    | true => exact (finiteAt f g ν θ hb hs ho).mpr (all g hg)
    | false =>
        obtain ⟨different,other⟩ := freshWires g hg hb
        exact (infiniteAt f g ν θ hb hs ho different other).mpr ⟨all g hg,assigned g hg hb⟩

theorem exactSharedWireList : ExactSharedWireList := by
  intro f gates fresh ν θ
  constructor
  · rintro ⟨normalized,agree⟩
    obtain ⟨original,assigned⟩ := (conjunction f gates fresh ν θ agree).mp normalized
    exact ⟨original,(exactWireListAssignments gates ν θ fresh.1).mp ⟨agree,assigned⟩⟩
  · rintro ⟨original,rfl⟩
    have agree := extendAgrees gates ν
    exact ⟨(conjunction f gates fresh ν (extend ν gates) agree).mpr
      ⟨original,extendPrescribed gates ν fresh.1⟩,agree⟩

theorem uniqueSharedWireList : UniqueSharedWireList := by
  intro f gates fresh ν
  have exactAt := exactSharedWireList f gates fresh ν
  refine ⟨?_,?_⟩
  · constructor
    · rintro ⟨θ,holds,_⟩
      exact ((exactAt θ).mp holds).1
    · intro real
      exact ⟨extend ν gates,(exactAt _).mpr ⟨real,rfl⟩,
        fun other holds => ((exactAt other).mp holds).2⟩
  · intro g hg
    exact ⟨extendAgrees gates ν g.source (fresh.2 g hg).1,
      extendAgrees gates ν g.output (fresh.2 g hg).2⟩

end LogicLineages.PermittedControl.ArbitraryHeadWireList
