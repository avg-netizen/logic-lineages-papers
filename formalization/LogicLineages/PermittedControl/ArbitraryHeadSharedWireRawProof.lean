module
public import LogicLineages.PermittedControl.ArbitraryHeadSharedWireTargets
import LogicLineages.PermittedControl.NaturalAffineGateGraphSemanticProof
import LogicLineages.OrdinalComparison.RawNormalProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadSharedWire
open OrdinalComparison

private theorem normalHead (a : NONote) : rawNormalCode (headCode a) = 1 :=
  (rawNormalCorrect a.1).mpr a.2

private theorem finiteRead (f : Nat → Nat) (a : NONote) (u : Nat)
    (finite : encodedFiniteTest (headCode a) = true) :
    ArbitraryFixedHeadCollapse.read f (headCode a,u) = some (encodedFiniteValue (headCode a) + u) := by
  rw [ArbitraryFixedHeadCollapse.read,if_pos (normalHead a),if_pos finite]

private theorem infiniteRead (f : Nat → Nat) (a : NONote) (u : Nat)
    (infinite : encodedFiniteTest (headCode a) = false) :
    ArbitraryFixedHeadCollapse.read f (headCode a,u) =
      FixedHeadCollapseGraph.read f (ArbitraryFixedHeadCollapse.transported (headCode a,u)) := by
  have skip : ¬ encodedFiniteTest (headCode a) = true := by rw [infinite]; decide
  rw [ArbitraryFixedHeadCollapse.read,if_pos (normalHead a),if_neg skip]

theorem exactFiniteWire : ExactFiniteWire := by
  intro f a finite source output ν
  rw [originalGraph,finiteRead f a (ν source) finite,
    NaturalAffineGateGraph.signedGraph output (finiteExpression a source) ν]
  simp only [Option.some.injEq,NaturalAffineGateGraph.signedValue,finiteExpression,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero]
  omega

private theorem exactShiftedInput (a : NONote) (source hidden : Nat) (ν : Valuation)
    (t : Nat) (fresh : hidden ≠ source) :
    (NaturalAffineGateGraph.graph hidden (shiftedExpression a source)).eval
        (Function.update ν hidden t) ↔
      t = (ArbitraryFixedHeadCollapse.transported (headCode a,ν source)).2 := by
  rw [NaturalAffineGateGraph.signedGraph hidden (shiftedExpression a source)
      (Function.update ν hidden t),Function.update_self]
  simp only [NaturalAffineGateGraph.signedValue,shiftedExpression,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,one_mul,add_zero,Function.update_of_ne fresh.symm]
  change (t : Int) = ((rawNormCode (limitCode a) + tailCode a : Nat) : Int) + (ν source : Int) ↔
    t = rawNormCode (limitCode a) + (tailCode a + ν source)
  rw [← Nat.cast_add, Nat.add_assoc]
  exact Int.ofNat_inj

theorem exactInfiniteWire : ExactInfiniteWire := by
  intro f a infinite source hidden output hSource hOutput ν
  let q := ArbitraryFixedHeadCollapse.transported (headCode a,ν source)
  have exactAt (t : Nat) :
      limitPair f a source hidden output (Function.update ν hidden t) ↔
        originalGraph f a source output ν ∧ t = q.2 := by
    unfold limitPair AffineCollapseGraphComposition.graph
    rw [exactShiftedInput a source hidden ν t hSource,Function.update_self,
      Function.update_of_ne hOutput.symm,originalGraph,infiniteRead f a (ν source) infinite]
    change (t = q.2 ∧ FixedHeadCollapseGraph.read f (q.1,t) = some (ν output)) ↔
      FixedHeadCollapseGraph.read f q = some (ν output) ∧ t = q.2
    constructor
    · rintro ⟨rfl,hit⟩
      exact ⟨hit,rfl⟩
    · rintro ⟨hit,rfl⟩
      exact ⟨rfl,hit⟩
  refine ⟨exactAt,?_,?_⟩
  · constructor
    · rintro ⟨t,holds,_⟩
      exact ((exactAt t).mp holds).1
    · intro holds
      refine ⟨q.2,(exactAt q.2).mpr ⟨holds,rfl⟩,?_⟩
      intro t hAt
      exact ((exactAt t).mp hAt).2
  · intro t n h
    exact Function.update_of_ne h t ν

end LogicLineages.PermittedControl.ArbitraryHeadSharedWire
