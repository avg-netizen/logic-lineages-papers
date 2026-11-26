module
public import LogicLineages.PermittedControl.InverseTableComparisonProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem actualInverseTable : Targets.ActualInverseTable := by
  intro f B hf lambda mu nu delta hll hm hn hd hml hgap x y hx hy
  let kappa := mu.1.repr+delta.1.repr
  let lambdaQ := nu.1.repr+delta.1.repr
  let sign := equalGapCertificateCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode delta.1)
  have hmu := normalRepresentationSound mu
  have hnu := normalRepresentationSound nu
  have hdelta := normalRepresentationSound delta
  have hlam := normalRepresentationSound lambda
  have hk : kappa<epsilonZero := epsilonZero_add_principal hmu hdelta
  have hq : lambdaQ<epsilonZero := epsilonZero_add_principal hnu hdelta
  have hkl : Order.IsSuccLimit kappa := Ordinal.isSuccLimit_add _ hd
  have hql : Order.IsSuccLimit lambdaQ := Ordinal.isSuccLimit_add _ hd
  have hmk : mu.1.repr<kappa := by
    simpa only [add_zero] using (add_lt_add_iff_left mu.1.repr).mpr hd.pos
  have hnq : nu.1.repr<lambdaQ := by
    simpa only [add_zero] using (add_lt_add_iff_left nu.1.repr).mpr hd.pos
  have hklam : kappa<lambda.1.repr := Ordinal.lt_sub.mp hgap
  have hdiff : lambdaQ-nu.1.repr=kappa-mu.1.repr := by
    dsimp only [lambdaQ,kappa]
    rw [Ordinal.add_sub_cancel,Ordinal.add_sub_cancel]
  let G := max 2 (max (actualOrdinalNorm lambda.1.repr)
    (max (actualOrdinalNorm kappa) (actualOrdinalNorm mu.1.repr)))
  let T := gapInputTail kappa mu.1.repr lambdaQ nu.1.repr 0
  let U := gapInputTail lambdaQ nu.1.repr kappa mu.1.repr 0
  let C := equalGapCertificateTailCode (rawNoteEncode mu.1) (rawNoteEncode nu.1)
    (rawNoteEncode delta.1) B
  have hxb : 1+max G (max T (max U C))≤x := hx
  have hyb : 1+max G (max T (max U C))≤y := hy
  obtain ⟨i,j,p,hi,hj,hp,hreset,hpij,hcont,hhi,hjN,hpN⟩ :=
    actualAffordableCocycle f B hf mu.1.repr kappa lambda.1.repr x hmu hk hlam hm hkl hll
      hmk hklam (by dsimp only [G] at hxb; omega)
  let h := entryNormAt f (countInitial lambda.1.repr x) i
  have hxh : x≤h := by
    change x≤entryNormAt f (countInitial lambda.1.repr x) i
    rw [hhi]
    exact iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i x
  have hh : 0<h := by omega
  have hTh : T≤h := by omega
  have hUh : U≤h := by omega
  have hCh : C≤h := by omega
  have hTm : T≤h-1 := by omega
  have hUm : U≤h-1 := by omega
  have hTp : T≤h+1 := by omega
  have hUp : U≤h+1 := by omega
  have hTy : T≤y := by omega
  have hUy : U≤y := by omega
  have hQtail := (gap_tail_bounds kappa mu.1.repr lambdaQ nu.1.repr 0).2.1
  obtain ⟨q,hqy,_⟩ := entryExistenceOrbit f B hf lambdaQ nu.1.repr y hq hql hn hnq (hQtail.trans hTy)
  obtain ⟨lo,hlo,_⟩ := entryExistenceOrbit f B hf lambdaQ nu.1.repr (h-1) hq hql hn hnq (hQtail.trans hTm)
  obtain ⟨mid,hmid,_⟩ := entryExistenceOrbit f B hf lambdaQ nu.1.repr h hq hql hn hnq (hQtail.trans hTh)
  obtain ⟨hiQ,hhiQ,_⟩ := entryExistenceOrbit f B hf lambdaQ nu.1.repr (h+1) hq hql hn hnq (hQtail.trans hTp)
  have hless : ∀ u z : Nat, T≤u → u<h → FirstEntry f (countInitial lambdaQ u) nu.1.repr z →
      entryNormAt f (countInitial lambdaQ u) z < entryNormAt f (countInitial lambda.1.repr x) p := by
    intro u z hu huh hz
    rw [hcont]
    exact inverse_input_comparison f B hf kappa mu.1.repr lambdaQ nu.1.repr hk hq hkl hql hm hn hmk hnq
      hdiff.le h u j z hTh hu huh hj hz
  have hgreater : ∀ u z : Nat, U≤u → h<u → FirstEntry f (countInitial lambdaQ u) nu.1.repr z →
      entryNormAt f (countInitial lambda.1.repr x) p < entryNormAt f (countInitial lambdaQ u) z := by
    intro u z hu huh hz
    rw [hcont]
    exact inverse_input_comparison f B hf lambdaQ nu.1.repr kappa mu.1.repr hq hk hql hkl hn hm hnq hmk
      hdiff.symm.le u h z j hu hUh huh hz hj
  obtain ⟨j',mid',hjt,hmt,hs0,hs1,hs2⟩ := equalGapSourceTail mu nu delta hm hn hd f B hf h hCh
  have ej : j'=j := firstEntry_unique f _ _ j' j hjt hj
  have em : mid'=mid := firstEntry_unique f _ _ mid' mid hmt hmid
  have hsignrange : sign≤2 := equalGapCertificateEffective.2.2 _ _ _
  have hcommon : numericalComparison (entryNormAt f (countInitial lambda.1.repr x) p)
      (entryNormAt f (countInitial lambdaQ h) mid)=sign := by
    rw [hcont]
    rcases (show sign=0 ∨ sign=1 ∨ sign=2 by omega) with hs | hs | hs
    · rw [hs]
      apply (numericalComparison_zero _ _).mpr
      simpa only [ej,em] using hs0 hs
    · rw [hs]
      apply (numericalComparison_one _ _).mpr
      simpa only [ej,em] using hs1 hs
    · rw [hs]
      apply (numericalComparison_two _ _).mpr
      simpa only [ej,em] using hs2 hs
  have hrows : InverseTableRows sign y h (entryNormAt f (countInitial lambdaQ y) q)
      (entryNormAt f (countInitial lambda.1.repr x) p) := by
    apply inverse_table_rows sign y h _ _ hh
    · intro hyh
      exact hless y q hTy hyh hqy
    · intro hhy
      exact hgreater y q hUy hhy hqy
    · intro he
      subst y
      have eqm := firstEntry_unique f _ _ q mid hqy hmid
      simpa only [eqm] using hcommon
  refine ⟨hmk,hklam,i,j,p,q,lo,mid,hiQ,hi,hxh,hh,hj,hp,hqy,hpij,hcont,hlo,hmid,hhiQ,
    hless (h-1) lo hTm (by omega) hlo,
    hgreater (h+1) hiQ hUp (by omega) hhiQ,hcommon,hrows,?_⟩
  intro hm0 hn0
  have hpartner : kappa=lambdaQ := by simp only [kappa,lambdaQ,hm0,hn0,zero_add]
  have hej : j=mid := firstEntry_unique f _ _ j mid (by simpa only [hpartner,hm0,hn0] using hj)
    (by simpa only [hn0] using hmid)
  have hv : entryNormAt f (countInitial lambda.1.repr x) p=entryNormAt f (countInitial lambdaQ h) mid := by
    rw [hcont]
    simp only [hpartner,hej,h]
  refine ⟨hpartner,?_⟩
  exact hcommon.symm.trans ((numericalComparison_one _ _).mpr hv)

end LogicLineages.PermittedControl
