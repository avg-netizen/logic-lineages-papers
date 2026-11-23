module
public import LogicLineages.StandardControlCurrent.PolicyIndexedPartialTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedPartialNodeProof
import LogicLineages.StandardControlCurrent.PolicyIndexedRankedLayerProof
import LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraphProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedPartial
open OrdinalComparison.Source.AdmissibleSum (Policy)
open ComputableRankedProof (graph bindList mapGraph)

private theorem frontierRank (s : Node) (k : Nat) :
    ∀ t ∈ bindList children s k, rank t < rank s + 1 - k := by
  induction k with
  | zero => simp [bindList]
  | succ k ih =>
    intro t ht
    change t ∈ (bindList children s k).flatMap children at ht
    obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp ht
    have h1 := ih c hc
    have h2 := exactIndexedPartialNode.1 c t ht
    omega

/-- Keep the same generic encoded equality instance used by mapGraph;
the raw product Node also has a different built-in BEq instance. -/
private theorem lookupAll {β σ : Type} [Primcodable β] (f : β → σ)
    {bs bs' : List β} (hsub : bs' ⊆ bs) :
    mapGraph (bs.map (fun x => (x,f x))) bs' = bs'.map f := by
  letI : DecidableEq β := Encodable.decidableEqOfEncodable β
  induction bs' with
  | nil => rfl
  | cons b bs' ih =>
    have both : b ∈ bs ∧ bs' ⊆ bs := by simpa using hsub
    simpa [mapGraph,List.lookup_graph f both.1] using ih both.2

private theorem graphLiteral (p : Policy) (s : Node) (fuel : Nat) (h : fuel ≤ rank s + 1) :
    graph rank children (typedNode p) s fuel =
      (bindList children s (rank s + 1 - fuel)).map
        (fun x => (x,PolicyPartial.run p x.1 x.2.1 x.2.2)) := by
  let f : Node → Value := fun x => PolicyPartial.run p x.1 x.2.1 x.2.2
  letI : DecidableEq Node := Encodable.decidableEqOfEncodable Node
  have nilFrontier : bindList children s (rank s + 1) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro b hb
    have hh := frontierRank s (rank s + 1) b hb
    omega
  have graphStep (i : Nat) :
      graph rank children (typedNode p) s (i+1) =
        (bindList children s (rank s-i)).filterMap (fun b =>
          (typedNode p b (mapGraph (graph rank children (typedNode p) s i) (children b))).map (b, ·)) := rfl
  have frontierStep (i : Nat) :
      bindList children s (i+1) = (bindList children s i).flatMap children := rfl
  change graph rank children (typedNode p) s fuel =
    (bindList children s (rank s+1-fuel)).map (fun x => (x,f x))
  induction fuel with
  | zero => simp [graph,nilFrontier]
  | succ i ih =>
    simp only [graphStep,ih (Nat.le_of_lt h),Nat.succ_sub (Nat.le_of_lt_succ h),
      Nat.succ_eq_add_one,frontierStep,Nat.reduceSubDiff]
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro b hb
    simp
    rw [lookupAll f]
    · exact exactIndexedPartialNode.2.1 p b
    · exact (List.infix_flatMap_of_mem hb children).subset

theorem exactIndexedPartialRun : ExactIndexedPartialRun := by
  intro c p hc s
  have hl := PolicyIndexedRankedLayer.exactIndexedLayer _ _ _ children assemble c
    (typedNode p) (exactIndexedPartialNode.2.2 c p hc)
  have hg := PolicyIndexedRankedGraph.exactPolicyIndexedRankedGraph _ _ _ rank children
    (PolicyIndexedRankedLayer.layer children assemble) c (typedNode p) hl
  unfold run
  rw [hg.2 s,graphLiteral p s (rank s + 1) (Nat.le_refl _)]
  simp [bindList]

end LogicLineages.StandardControlCurrent.PolicyIndexedPartial
