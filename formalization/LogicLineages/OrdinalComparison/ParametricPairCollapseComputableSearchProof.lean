module
public import LogicLineages.OrdinalComparison.ParametricPairCollapseComputableTargets
public import LogicLineages.OrdinalComparison.ParametricPairMachineCodeProof
public import LogicLineages.OrdinalComparison.ParametricPairWorklistProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairCollapseComputable.Proof
open ParametricPairMachineCode ParametricPairWorklist

theorem exactSearch : Targets.ExactSearch := by
  intro H p
  have hc := (ParametricPairMachineCode.Proof.exactCalibration H).2.2.2 p.1 p.2
  have hs := ParametricPairWorklist.Proof.exactSuccess (fun n => H (p.1,n)) p.2
  have sound : ∀ k n, indexedEvaluate H p.1 p.2 k=some n → n=actualValue H p := by
    intro k n hn
    rw [hc k] at hn
    exact hs.1 k n hn
  obtain ⟨N,hN⟩ := hs.2.1
  have hN' : indexedEvaluate H p.1 p.2 N=some (actualValue H p) := (hc N).trans hN
  have hd : (searchValue H p).Dom := by
    apply Nat.rfindOpt_dom.mpr
    exact ⟨N,actualValue H p,by simp [hN']⟩
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨k,hk⟩ := Nat.rfindOpt_spec hv
  have hval : v=actualValue H p := sound k v (by simpa using hk)
  subst v
  refine ⟨hv,hd,?_,?_⟩
  · intro n
    exact ⟨fun hn => Part.mem_unique hn hv,fun hn => hn ▸ hv⟩
  · obtain ⟨fuel,_,hf,hearlier⟩ := hs.2.2
    refine ⟨fuel,(hc fuel).trans hf,?_⟩
    intro k hk
    exact (hc k).trans (hearlier k hk)

attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt
  ParametricPairMachineCode.indexedEvaluate

theorem uniformPartialRecursive : Targets.UniformPartialRecursive := by
  intro H hH
  have he : Computable (fun p : (Nat × (Nat × Nat)) × Nat =>
      indexedEvaluate H p.1.1 p.1.2 p.2) :=
    (ParametricPairMachineCode.Proof.indexedComputable H hH).2.2
  exact Partrec.rfindOpt he.to₂
end LogicLineages.OrdinalComparison.Source.ParametricPairCollapseComputable.Proof
