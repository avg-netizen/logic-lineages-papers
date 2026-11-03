module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedKeyTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.HeterogeneousHeadProof
public import LogicLineages.OrdinalComparison.HeadWindowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.KeyProof

private theorem key_trichotomy (basis:List Nat) (a b:Atom):
    keyLess basis a b∨keyEqual basis a b∨keyLess basis b a:=by
  unfold keyLess keyEqual actualHeadKeyLess
  rcases lt_trichotomy a.head.1.repr b.head.1.repr with h|h|h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (input basis a) (input basis b) with ht|ht|ht
    · exact Or.inl (Or.inr ⟨h,ht⟩)
    · exact Or.inr (Or.inl ⟨h,ht⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm,ht⟩))
  · exact Or.inr (Or.inr (Or.inl h))

theorem actualKeyWindow:KeyTargets.ActualKeyWindow:=by
  intro basis row hf hg hlarge selected hs hmin
  have hw:=(Proof.largeWindow basis row hf hlarge selected hs hmin).1
  have domain:∀a∈row.atoms,actualOrdinalNorm a.2.head.1.repr≤ input basis a.2:=by
    intro a ha
    have h:=hw a ha
    omega
  have strict:∀a∈row.atoms,∀b∈row.atoms,keyLess basis a.2 b.2→
      atomValue basis a.2<atomValue basis b.2∧atomEndpoint basis a.2<atomEndpoint basis b.2:=by
    intro a ha b hb hk
    have hwa:=hw a ha
    have hwb:=hw b hb
    have hda:=domain a ha
    have hdb:=domain b hb
    rcases hk with hhead|⟨heq,hin⟩
    · exact actualDifferentHeadStrictWindow b.2.head.1.repr a.2.head.1.repr
        (rawNotation_repr_lt_epsilonZero b.2.head.1) (rawNotation_repr_lt_epsilonZero a.2.head.1)
        (hg b hb) (hg a ha) hhead (input basis b.2) (input basis a.2)
        hdb (hwa.1.trans hwb.2.1) hda
        (hwa.2.2.trans_le (Phi_strictMono.monotone hwb.2.1))
    · have hda':actualOrdinalNorm b.2.head.1.repr≤ input basis a.2:=heq ▸ hda
      have h:=actualFixedHeadValueEndpointOrder b.2.head.1.repr
        (rawNotation_repr_lt_epsilonZero b.2.head.1) (hg b hb)
        (input basis a.2) (input basis b.2) hda' hdb hin
      simpa only [atomValue,atomEndpoint,heq] using h
  intro a ha b hb
  have hkeys:=key_trichotomy basis a.2 b.2
  have hval:atomValue basis a.2<atomValue basis b.2↔keyLess basis a.2 b.2:=by
    constructor
    · intro h
      rcases hkeys with hk|⟨heq,hin⟩|hk
      · exact hk
      · simp only [atomValue,heq,hin] at h
        exact False.elim (Nat.lt_irrefl _ h)
      · exact False.elim (Nat.lt_asymm h (strict b hb a ha hk).1)
    · intro hk
      exact (strict a ha b hb hk).1
  have hend:atomEndpoint basis a.2<atomEndpoint basis b.2↔keyLess basis a.2 b.2:=by
    constructor
    · intro h
      rcases hkeys with hk|⟨heq,hin⟩|hk
      · exact hk
      · simp only [atomEndpoint,heq,hin] at h
        exact False.elim (Nat.lt_irrefl _ h)
      · exact False.elim (Nat.lt_asymm h (strict b hb a ha hk).2)
    · intro hk
      exact (strict a ha b hb hk).2
  have heq:atomEndpoint basis a.2=atomEndpoint basis b.2↔keyEqual basis a.2 b.2:=by
    constructor
    · intro h
      rcases hkeys with hk|heq|hk
      · exact False.elim ((Nat.ne_of_lt (strict a ha b hb hk).2) h)
      · exact heq
      · exact False.elim ((Nat.ne_of_lt (strict b hb a ha hk).2) h.symm)
    · rintro ⟨heq,hin⟩
      simp only [atomEndpoint,heq,hin]
  have ba:=HeterogeneousHead.Proof.actualBand a.2.head (hg a ha) (input basis a.2) (domain a ha)
  have bb:=HeterogeneousHead.Proof.actualBand b.2.head (hg b hb) (input basis b.2) (domain b hb)
  have hindex:atomIndex basis a.2<atomIndex basis b.2↔atomEndpoint basis a.2<atomEndpoint basis b.2:=by
    unfold atomIndex atomEndpoint
    rw [ba.2.1,bb.2.1]
    exact Phi_strictMono.lt_iff_lt.symm
  have hindexeq:atomIndex basis a.2=atomIndex basis b.2↔atomEndpoint basis a.2=atomEndpoint basis b.2:=by
    unfold atomIndex atomEndpoint
    rw [ba.2.1,bb.2.1]
    exact Phi_strictMono.injective.eq_iff.symm
  exact ⟨hval,hend,hindex.trans hend,hindexeq.trans heq⟩
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.KeyProof
