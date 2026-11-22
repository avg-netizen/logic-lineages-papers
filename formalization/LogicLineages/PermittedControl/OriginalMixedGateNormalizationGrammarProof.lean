module
public import LogicLineages.PermittedControl.OriginalMixedGateNormalizationTargets
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationFreshProof
import LogicLineages.PermittedControl.OriginalMixedGateSequentialReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedGateNormalization
open ArbitraryHeadSharedWire (Valuation originalGraph)
open ArbitraryHeadFreshWireAllocation (Wire attach install strip OriginalConjunction)
open ArbitraryHeadWireList (NormalGate normalizeGate NormalizedAt OriginalAt)
open OriginalMixedGateSequential (Gate Graphs readCongruent exactMixedGateRead)

private theorem holdsCons (f : Nat → Nat) (θ : Valuation) (p : NormalGate) (ps : List NormalGate) :
    Holds f θ (p :: ps) ↔ p.Holds f θ ∧ Holds f θ ps := by
  constructor
  · intro h
    exact ⟨h p List.mem_cons_self,fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
  · rintro ⟨head,tail⟩ q hq
    rcases List.mem_cons.mp hq with eq | rest
    · subst q
      exact head
    · exact tail q rest

private theorem normalizedCons (f : Nat → Nat) (θ : Valuation)
    (g : ArbitraryHeadWireList.Gate) (gs : List ArbitraryHeadWireList.Gate) :
    NormalizedAt f θ (g :: gs) ↔ (normalizeGate g).Holds f θ ∧ NormalizedAt f θ gs :=
  holdsCons f θ (normalizeGate g) (ArbitraryHeadWireList.normalize gs)

theorem normalizedSplit (f : Nat → Nat) (θ : Valuation) (gates : List Gate) (n : Nat) :
    Holds f θ (normalizeFrom n gates) ↔
      AffinesAt θ gates ∧ NormalizedAt f θ (attach n (collapseWires gates)) := by
  induction gates generalizing n with
  | nil => simp [Holds,normalizeFrom,AffinesAt,NormalizedAt,attach,collapseWires,
      ArbitraryHeadWireList.normalize]
  | cons g gs ih =>
      cases g with
      | affine e out =>
          change Holds f θ (NormalGate.affine e out :: normalizeFrom n gs) ↔
            ((NaturalAffineGateGraph.graph out e).eval θ ∧ AffinesAt θ gs) ∧
              NormalizedAt f θ (attach n (collapseWires gs))
          rw [holdsCons,ih]
          exact and_assoc.symm
      | collapse w =>
          change Holds f θ (normalizeGate (install w n) :: normalizeFrom (n+1) gs) ↔
            AffinesAt θ gs ∧ NormalizedAt f θ (install w n :: attach (n+1) (collapseWires gs))
          rw [holdsCons,ih,normalizedCons]
          constructor
          · rintro ⟨hd,ha,ht⟩
            exact ⟨ha,hd,ht⟩
          · rintro ⟨ha,hd,ht⟩
            exact ⟨hd,ha,ht⟩

private theorem originalCons (f : Nat → Nat) (θ : Valuation) (g : Gate) (gs : List Gate) :
    Graphs f θ (g :: gs) ↔ g.graph f θ ∧ Graphs f θ gs := by
  constructor
  · intro h
    exact ⟨h g List.mem_cons_self,fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
  · rintro ⟨hd,ht⟩ p hp
    rcases List.mem_cons.mp hp with eq | rest
    · subst p
      exact hd
    · exact ht p rest

private theorem wireCons (f : Nat → Nat) (θ : Valuation) (w : Wire) (ws : List Wire) :
    OriginalConjunction f θ (w :: ws) ↔
      originalGraph f w.head w.source w.output θ ∧ OriginalConjunction f θ ws := by
  constructor
  · intro h
    exact ⟨h w List.mem_cons_self,fun v hv => h v (List.mem_cons_of_mem _ hv)⟩
  · rintro ⟨hd,ht⟩ p hp
    rcases List.mem_cons.mp hp with eq | rest
    · subst p
      exact hd
    · exact ht p rest

private theorem originalSplit (f : Nat → Nat) (θ : Valuation) (gates : List Gate) :
    Graphs f θ gates ↔ AffinesAt θ gates ∧ OriginalConjunction f θ (collapseWires gates) := by
  induction gates with
  | nil => simp [Graphs,AffinesAt,collapseWires,OriginalConjunction]
  | cons g gs ih =>
      rw [originalCons,ih]
      cases g with
      | affine e out =>
          change (NaturalAffineGateGraph.graph out e).eval θ ∧
            (AffinesAt θ gs ∧ OriginalConjunction f θ (collapseWires gs)) ↔
            ((NaturalAffineGateGraph.graph out e).eval θ ∧ AffinesAt θ gs) ∧
              OriginalConjunction f θ (collapseWires gs)
          exact and_assoc.symm
      | collapse w =>
          change originalGraph f w.head w.source w.output θ ∧
            (AffinesAt θ gs ∧ OriginalConjunction f θ (collapseWires gs)) ↔
            AffinesAt θ gs ∧ OriginalConjunction f θ (w :: collapseWires gs)
          rw [wireCons]
          constructor
          · rintro ⟨hd,ha,ht⟩
            exact ⟨ha,hd,ht⟩
          · rintro ⟨ha,hd,ht⟩
            exact ⟨hd,ha,ht⟩

private theorem attachReads (f : Nat → Nat) (θ : Valuation) (wires : List Wire) (n : Nat) :
    OriginalAt f θ (attach n wires) ↔ OriginalConjunction f θ wires := by
  have shape := attachShape wires n
  constructor
  · intro original w hw
    rw [← shape] at hw
    obtain ⟨g,hg,eq⟩ := List.mem_map.mp hw
    subst w
    exact original g hg
  · intro original q hq
    have h : strip q ∈ wires := by
      rw [← shape]
      exact List.mem_map.mpr ⟨q,hq,rfl⟩
    exact original (strip q) h

theorem originalAttached (f : Nat → Nat) (θ : Valuation) (gates : List Gate) (n : Nat) :
    Graphs f θ gates ↔ AffinesAt θ gates ∧ OriginalAt f θ (attach n (collapseWires gates)) :=
  (originalSplit f θ gates).trans (and_congr Iff.rfl (attachReads f θ (collapseWires gates) n).symm)

theorem affinesCongruent (f : Nat → Nat) (ν θ : Valuation) (gates : List Gate)
    (same : ∀ g ∈ gates, θ g.output = ν g.output ∧ ∀ n ∈ g.references, θ n = ν n) :
    AffinesAt θ gates ↔ AffinesAt ν gates := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      have htail := ih (fun p hp => same p (List.mem_cons_of_mem _ hp))
      cases g with
      | collapse w => exact htail
      | affine e out =>
          have hw := same (Gate.affine e out) List.mem_cons_self
          have read := readCongruent f (Gate.affine e out) ν θ hw.2
          have q : (Gate.affine e out).read f θ = some (θ (Gate.affine e out).output) ↔
              (Gate.affine e out).read f ν = some (ν (Gate.affine e out).output) := by
            rw [read,hw.1]
          have ha := ((exactMixedGateRead.1 f θ (Gate.affine e out)).symm.trans q).trans
            (exactMixedGateRead.1 f ν (Gate.affine e out))
          exact and_congr ha htail

end LogicLineages.PermittedControl.OriginalMixedGateNormalization
