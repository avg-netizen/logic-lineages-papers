module
public import LogicLineages.OrdinalComparison.ComparisonSourceDomainTargets
public import LogicLineages.OrdinalComparison.PositiveSourceDataImageProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonSourceDomain

theorem primitive : Targets.ComparisonSourceDomainPrimitiveRecursive := by
  have hn : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hp : PrimrecPred (fun p : Nat × Nat => rawNormalCode p.1=1 ∧ p.1≠0) :=
    (Primrec.eq.comp (hn.comp Primrec.fst) (Primrec.const 1)).and
      ((Primrec.eq.comp Primrec.fst (Primrec.const 0)).not)
  have hentries : PrimrecPred comparisonRawKernelEntriesValid := hp.forall_mem_list
  have hm := Primrec.nat_mod.comp Primrec.id (Primrec.const 2)
  have hd := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hfields := Primrec.unpair.comp hd
  have hw : Primrec (fun n : Nat =>
      (Encodable.decode (α := List (Nat × Nat)) (n/2).unpair.1).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp hfields)) (Primrec.const [])
  have hdata := PositiveSourceDomain.data_primitive.comp (Primrec.snd.comp hfields)
  have hguard := ((Primrec.eq.comp hw (Primrec.const [])).not).and
    ((Primrec.eq.comp (Primrec.encode.comp hw) (Primrec.fst.comp hfields)).and
      ((hentries.comp hw).and ((Primrec.eq.comp (Primrec.fst.comp hdata) (Primrec.const 1)).and
        (Primrec.eq.comp (Primrec.snd.comp hdata) (Primrec.const 1)))))
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0))
    (Primrec.fst.comp (PositiveSourceDomain.data_primitive.comp hd))
    (Primrec.ite hguard (Primrec.const 1) (Primrec.const 0))

private theorem positive_code_ne_zero (eta : NONote) (hp : 0<eta.1.repr) : rawNoteEncode eta.1≠0 := by
  intro hc
  have hh := congrArg rawNoteDecode hc
  rw [rawNoteDecodeEncode eta.1] at hh
  have hzero : eta.1=ONote.zero := by simpa only [rawNoteDecode] using hh
  rw [hzero] at hp
  exact lt_irrefl _ hp

theorem correct : Targets.ComparisonSourceDomainCorrect := by
  intro A hv
  cases A with
  | positive E =>
    have hm : (2*positiveExprEncode E)%2=0 := by omega
    have hd : (2*positiveExprEncode E)/2=positiveExprEncode E := by omega
    simpa only [encodedComparisonSourceDomain,oneVariableComparisonEncode,hm,hd,if_true] using
      (PositiveSourceDomain.data_program.2 E).1.mpr hv
  | range w E =>
    let word := encodePrincipalKernelWord (comparisonRawWord w)
    let payload := Nat.pair (Encodable.encode word) (positiveExprEncode E)
    have hm : (2*payload+1)%2=1 := by omega
    have hd : (2*payload+1)/2=payload := by omega
    have hn : word≠[] := by
      cases w with
      | nil => exact (hv.1 rfl).elim
      | cons p w => simp [word,encodePrincipalKernelWord,comparisonRawWord]
    have hentries : comparisonRawKernelEntriesValid word := by
      intro p hp
      simp only [word,encodePrincipalKernelWord,comparisonRawWord,List.map_map] at hp
      rcases List.mem_map.mp hp with ⟨q,hq,rfl⟩
      exact ⟨(rawNormalCorrect q.1.1).mpr q.1.2,positive_code_ne_zero q.1 (hv.2.1 q hq)⟩
    have hdata := (PositiveSourceDomain.data_program.2 E).1.mpr hv.2.2.1
    have hinput : (encodedPositiveSourceData (positiveExprEncode E)).2=1 := by
      rw [(PositiveSourceDomain.data_program.2 E).2,hv.2.2.2]
      rfl
    have hencode : oneVariableComparisonEncode (.range w E)=2*payload+1 := rfl
    change (if (2*payload+1)%2=0 then _ else _)=1
    simp only [hencode,hm,Nat.one_ne_zero,if_false,hd,payload,Nat.unpair_pair,Encodable.encodek,Option.getD_some]
    exact (PositiveSourceDomain.flag_correct _).mpr ⟨hn,True.intro,hentries,hdata,hinput⟩

end LogicLineages.OrdinalComparison.ComparisonSourceDomain
