module
public import LogicLineages.OrdinalComparison.OneVariableComparisonDomainsProof
public import LogicLineages.OrdinalComparison.EncodedKernelWordProof
public import LogicLineages.OrdinalComparison.PositiveInputPlugProof
public import LogicLineages.OrdinalComparison.RawNormCode

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneVariableComparison

attribute [local irreducible] Phi actualCollapse encodedPositiveEvaluation encodedKernelWordRun

private theorem word_bound_primitive : Primrec encodedComparisonWordDomainBound := by
  have he : Primrec (fun p : List (Nat × Nat) × ((Nat × Nat) × Nat) => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hc : Primrec (fun p : List (Nat × Nat) × ((Nat × Nat) × Nat) => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec (fun p : List (Nat × Nat) × ((Nat × Nat) × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hs : Primrec₂ (fun _ : List (Nat × Nat) => fun q : (Nat × Nat) × Nat =>
      max (q.1.2+1+rawNormCode q.1.1) q.2) :=
    Primrec.nat_max.comp (Primrec.nat_add.comp (Primrec.succ.comp hc) (hn.comp he)) ht
  have h := Primrec.list_foldr Primrec.id (Primrec.const 1) hs
  apply h.of_eq
  intro w
  induction w with
  | nil => rfl
  | cons p w ih =>
    change max (p.2+1+rawNormCode p.1)
      (w.foldr (fun q acc => max (q.2+1+rawNormCode q.1) acc) 1)=_
    change w.foldr (fun q acc => max (q.2+1+rawNormCode q.1) acc) 1=
      encodedComparisonWordDomainBound w at ih
    rw [ih]
    rfl

private theorem bound_primitive : Primrec encodedOneVariableComparisonDomainBound := by
  have hm := Primrec.nat_mod.comp Primrec.id (Primrec.const 2)
  have hp := Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  have hw : Primrec (fun n : Nat =>
      (Encodable.decode (α := List (Nat × Nat)) (n/2).unpair.1).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp hp)) (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const 1)
    (word_bound_primitive.comp hw)

private theorem value_computable : Computable₂ encodedOneVariableComparisonValue := by
  have hn : Primrec (fun p : Nat × Nat => p.1) := Primrec.fst
  have hx : Primrec (fun p : Nat × Nat => p.2) := Primrec.snd
  have hd := Primrec.nat_div.comp hn (Primrec.const 2)
  have hp := Primrec.unpair.comp hd
  have hw : Computable (fun p : Nat × Nat =>
      (Encodable.decode (α := List (Nat × Nat)) (p.1/2).unpair.1).getD []) :=
    (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp hp)) (Primrec.const [])).to_comp
  have hP : Computable (fun p : Nat × Nat => encodedPositiveEvaluation (p.1/2) p.2) :=
    encodedPositiveEvaluationComputable.comp hd.to_comp hx.to_comp
  have harg : Computable (fun p : Nat × Nat =>
      encodedPositiveEvaluation (p.1/2).unpair.2 p.2) :=
    encodedPositiveEvaluationComputable.comp (Primrec.snd.comp hp).to_comp hx.to_comp
  have hR : Computable (fun p : Nat × Nat =>
      (encodedKernelWordRun ((Encodable.decode (α := List (Nat × Nat)) (p.1/2).unpair.1).getD [])
        (encodedPositiveEvaluation (p.1/2).unpair.2 p.2)).1) :=
    Computable.fst.comp (encodedKernelWordComputable.comp hw harg)
  have ht : PrimrecPred (fun p : Nat × Nat => p.1%2=0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 2)) (Primrec.const 0)
  change Computable (fun p : Nat × Nat => encodedOneVariableComparisonValue p.1 p.2)
  simpa only [encodedOneVariableComparisonValue,Bool.cond_decide] using
    Computable.cond ht.decide.to_comp hP hR

private theorem word_bound_correct (w : List (NONote × Nat)) :
    encodedComparisonWordDomainBound (encodePrincipalKernelWord (comparisonRawWord w))=
      comparisonWordDomainBound w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨eta,c⟩
    change max (c+1+rawNormCode (rawNoteEncode eta.1))
      (encodedComparisonWordDomainBound (encodePrincipalKernelWord (comparisonRawWord w)))=
      max (c+1+Vendor.R1.treeWeight eta.1) (comparisonWordDomainBound w)
    rw [rawNormCodeCorrect eta.1,ih]

theorem source_program : Targets.OneVariableComparisonSourceProgram := by
  refine ⟨bound_primitive,value_computable,?_⟩
  intro E hv
  cases E with
  | positive E =>
    have hm : (2*positiveExprEncode E)%2=0 := by omega
    have hd : (2*positiveExprEncode E)/2=positiveExprEncode E := by omega
    refine ⟨?_,Nat.le_refl _,?_⟩
    · simp only [oneVariableComparisonEncode,encodedOneVariableComparisonDomainBound,hm,
        if_true,oneVariableComparisonDomainBound]
    · intro x _
      refine ⟨True.intro,?_⟩
      simpa only [oneVariableComparisonEncode,encodedOneVariableComparisonValue,hm,
        if_true,hd,actualOneVariableComparisonValue] using encodedPositiveEvaluationCorrect E x
  | range w E =>
    let q := Nat.pair (Encodable.encode (encodePrincipalKernelWord (comparisonRawWord w))) (positiveExprEncode E)
    have hm : (2*q+1)%2=1 := by omega
    have hd : (2*q+1)/2=q := by omega
    have hb : encodedOneVariableComparisonDomainBound (oneVariableComparisonEncode (.range w E))=
        comparisonWordDomainBound w := by
      change (if (2*q+1)%2=0 then 1 else
        encodedComparisonWordDomainBound
          ((Encodable.decode (α := List (Nat × Nat)) ((2*q+1)/2).unpair.1).getD []))=_
      rw [hm,hd]
      norm_num only
      simpa only [q,Nat.unpair_pair,Encodable.encodek,Option.getD_some,if_false] using word_bound_correct w
    refine ⟨hb,word_bound_positive w,?_⟩
    intro x hx
    have harg : comparisonWordDomainBound w≤actualFixedLimitProfileEval E x :=
      hx.trans (open_lower E hv.2.2.1 hv.2.2.2 x)
    have hg := (word_domains w _ harg).1
    refine ⟨hg,?_⟩
    have hw : ∀ p∈comparisonRawWord w, ONote.NF p.1 ∧ 0<p.1.repr := by
      intro p hp
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
      exact ⟨r.1.2,hv.2.1 r hr⟩
    have he := encodedKernelWordCorrect (comparisonRawWord w) hw (actualFixedLimitProfileEval E x) hg
    change (if (2*q+1)%2=0 then encodedPositiveEvaluation ((2*q+1)/2) x else
      (encodedKernelWordRun ((Encodable.decode (α := List (Nat × Nat)) ((2*q+1)/2).unpair.1).getD [])
        (encodedPositiveEvaluation ((2*q+1)/2).unpair.2 x)).1)=_
    rw [hm,hd]
    norm_num only
    simpa only [q,Nat.unpair_pair,Encodable.encodek,Option.getD_some,
      if_false,encodedPositiveEvaluationCorrect E x,actualOneVariableComparisonValue] using congrArg Prod.fst he

end LogicLineages.OrdinalComparison.OneVariableComparison
