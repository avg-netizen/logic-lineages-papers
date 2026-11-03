module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedDominanceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedKeyProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumericalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.DominanceProof

private theorem square_le_power (n:Nat) (hn:4≤n):n*n≤2^n:=by
  induction n,hn using Nat.le_induction with
  | base=>decide
  | succ n hn ih=>
    have hp:(n+1)*(n+1)≤2*(n*n):=by nlinarith
    calc
      (n+1)*(n+1)≤2*(n*n):=hp
      _≤2*2^n:=Nat.mul_le_mul_left 2 ih
      _=2^(n+1):=by rw [Nat.pow_succ,Nat.mul_comm]

private theorem quadratic_phi (n:Nat) (hn:4≤n):n*n≤Phi n:=
  (square_le_power n hn).trans
    ((Nat.pow_le_pow_right (by decide) (by omega :n≤n+100)).trans (two_pow_shift_le_Phi n))

theorem actualDominance:DominanceTargets.ActualSurvivingDominance:=by
  intro basis row hf hg hpair hlarge selected hs hmin winner hwinner hnonzero hmax
  have keys:=KeyProof.actualKeyWindow basis row hf hg hlarge selected hs hmin
  have windows:=Proof.largeWindow basis row hf hlarge selected hs hmin
  let nums:CommonHeadLargeRow.NumericalRow:=row.atoms.map
    (fun a=>(a.1,atomValue basis a.2,atomIndex basis a.2))
  have mass:CommonHeadLargeRow.numericalMass nums=coefficientMass row:=by
    simp only [CommonHeadLargeRow.numericalMass,nums,coefficientMass,List.map_map,Function.comp_def]
  have pairwise:nums.Pairwise (fun a b=>a.2.2≠b.2.2):=by
    dsimp only [nums]
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem (p:=hpair)
    intro a b ha hb hne heq
    exact hne ((keys a ha b hb).2.2.2.mp heq)
  have budget:max 4 (2*coefficientMass row)≤threshold row:=by
    unfold threshold BalancedNumerical.threshold
    omega
  have bands:∀a∈nums,max 4 (2*CommonHeadLargeRow.numericalMass nums)≤a.2.2∧
      Phi a.2.2<a.2.1∧a.2.1<2*Phi a.2.2:=by
    intro a ha
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
    have domain:actualOrdinalNorm b.2.head.1.repr≤ input basis b.2:=by
      unfold input normOffset
      omega
    have band:=HeterogeneousHead.Proof.actualBand b.2.head (hg b hb) (input basis b.2) domain
    refine ⟨?_,band.2.2⟩
    rw [mass]
    exact (budget.trans (hlarge b hb)).trans band.1
  have winnerMem:(winner.1,atomValue basis winner.2,atomIndex basis winner.2)∈nums:=
    List.mem_map.mpr ⟨winner,hwinner,rfl⟩
  have maximum:∀a∈nums,a.2.2≤atomIndex basis winner.2:=by
    intro a ha
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
    have hn:¬atomIndex basis winner.2<atomIndex basis b.2:=by
      intro h
      exact hmax b hb ((keys winner hwinner b hb).2.2.1.mp h)
    change atomIndex basis b.2≤atomIndex basis winner.2
    exact Nat.le_of_not_gt hn
  have hinput:4≤ input basis winner.2:=by
    have h:=budget.trans (hlarge winner hwinner)
    omega
  have hindex:input basis winner.2≤atomIndex basis winner.2:=by
    have domain:actualOrdinalNorm winner.2.head.1.repr≤ input basis winner.2:=by
      unfold input normOffset
      omega
    exact (HeterogeneousHead.Proof.actualBand winner.2.head (hg winner hwinner)
      (input basis winner.2) domain).1
  have remainder:4*(remainderValue basis row).natAbs<Phi (atomIndex basis winner.2):=
    (windows.2 winner hwinner).trans_le
      ((quadratic_phi (input basis winner.2) hinput).trans (Phi_strictMono.monotone hindex))
  have sign:=BalancedNumerical.Proof.survivingDominance (remainderValue basis row)
    nums pairwise bands (winner.1,atomValue basis winner.2,atomIndex basis winner.2)
    winnerMem hnonzero maximum remainder
  change Int.sign _=Int.sign winner.1 at sign
  simpa only [CommonHeadLargeRow.numericalValue,nums,value,atomValue,List.map_map,Function.comp_def] using sign
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.DominanceProof
