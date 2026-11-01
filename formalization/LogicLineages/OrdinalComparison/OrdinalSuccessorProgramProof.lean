module
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramTargets
public import LogicLineages.OrdinalComparison.RawSplitProof
public import LogicLineages.OrdinalComparison.EncodedFiniteTailProof
public import LogicLineages.OrdinalComparison.ComparisonSignatureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OrdinalSuccessorProgram

theorem primitive : Targets.OrdinalSuccessorProgramsPrimitiveRecursive := by
  have hs : Primrec (fun n : Nat => (rawSplitCode n).unpair) :=
    Primrec.unpair.comp (Primrec.nat_iff.mpr rawSplitPrimitiveRecursive)
  exact ⟨Primrec.snd.comp hs,
    encodedFiniteTailPrimitiveRecursive.comp (Primrec.fst.comp hs)
      (Primrec.pred.comp (Primrec.snd.comp hs))⟩

theorem predecessor : Targets.ActualOrdinalSuccessorPredecessorProgram := by
  intro eta ht
  letI := eta.2
  rcases hs : ONote.split eta.1 with ⟨l,n⟩
  have hN := ONote.nf_repr_split hs
  let limit : NONote := ⟨l,hN.1⟩
  let pred := finiteTail limit (n-1)
  have hn : 0<n := by
    simpa only [encodedOrdinalFiniteRemainder,rawSplitCorrect eta.1,hs,Nat.unpair_pair] using ht
  have hsucc : eta.1.repr=pred.1.repr+1 := by
    calc
      eta.1.repr=l.repr+(n:Ordinal) := hN.2
      _ = (l.repr+((n-1:Nat):Ordinal))+1 := by
        have hnEq : n=(n-1)+1 := by omega
        simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using
          congrArg (fun k : Nat => l.repr+(k:Ordinal)) hnEq
      _ = pred.1.repr+1 := by rw [(finiteTailCorrect limit (n-1)).1]
  refine ⟨pred,?_,hsucc,ComparisonSignature.successor_closure.1 eta pred hsucc⟩
  simp only [encodedOrdinalSuccessorPredecessor,rawSplitCorrect eta.1,hs,Nat.unpair_pair]
  exact (encodedFiniteTailCorrect limit (n-1)).1

theorem classification : Targets.ActualOrdinalFiniteRemainderClassification := by
  intro eta
  constructor
  · intro ht
    letI := eta.2
    rcases hs : ONote.split eta.1 with ⟨l,n⟩
    have hN := ONote.nf_repr_split hs
    have hn : n=0 := by
      simpa only [encodedOrdinalFiniteRemainder,rawSplitCorrect eta.1,hs,Nat.unpair_pair] using ht
    have hd : Ordinal.omega0∣eta.1.repr := by
      have hrepr : eta.1.repr=l.repr := by simpa only [hn,Nat.cast_zero,add_zero] using hN.2
      rw [hrepr]
      exact ONote.split_dvd hs
    have hpre := Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr hd
    by_cases hz : eta.1.repr=0
    · exact Or.inl hz
    · exact Or.inr (Order.isSuccLimit_iff_of_orderBot.mpr ⟨hz,hpre⟩)
  · intro h
    by_contra hn
    obtain ⟨pred,_,hs,_⟩ := predecessor eta (Nat.pos_of_ne_zero hn)
    rcases h with hz | hl
    · have hpos : (0:Ordinal)<eta.1.repr := by
        rw [hs]
        exact lt_of_le_of_lt bot_le (lt_add_one _)
      rw [hz] at hpos
      exact lt_irrefl _ hpos
    · apply hl.isSuccPrelimit.succ_ne pred.1.repr
      simpa only [Order.succ_eq_add_one] using hs.symm

theorem no_jump : Targets.ActualOrdinalSuccessorNoJump := by
  intro eta lower hlt ht
  obtain ⟨pred,hcode,hs,hweight⟩ := predecessor eta ht
  refine ⟨pred,hcode,hs,?_,hweight⟩
  rw [hs] at hlt
  exact Order.lt_add_one_iff.mp hlt

end LogicLineages.OrdinalComparison.OrdinalSuccessorProgram
