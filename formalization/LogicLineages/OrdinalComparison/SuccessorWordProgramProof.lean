module
public import LogicLineages.OrdinalComparison.SuccessorWordProgramTargets
public import LogicLineages.OrdinalComparison.OneVariableComparisonProgramProof
public import LogicLineages.OrdinalComparison.SuccessorKernelsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SuccessorWordProgram

private theorem principal_norm (eta : NONote) :
    actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=1+Vendor.R1.treeWeight eta.1 := by
  letI := eta.2
  let o : NONote := ⟨ONote.oadd eta.1 1 0,inferInstance⟩
  simpa [o,ONote.repr,Vendor.R1.treeWeight] using actualOrdinalNorm_notationCorrespondence o

private theorem principal_below (eta : NONote) : Ordinal.omega0^eta.1.repr<epsilonZero := by
  letI := eta.2
  let o : NONote := ⟨ONote.oadd eta.1 1 0,inferInstance⟩
  simpa [o,ONote.repr] using normalRepresentationSound o

private theorem word_append (v w : List (ONote × Nat)) (t : Nat) :
    actualPrincipalWordRun (v++w) t=
      ((actualPrincipalWordRun w (actualPrincipalWordRun v t).1).1,
       (actualPrincipalWordRun v t).2+(actualPrincipalWordRun w (actualPrincipalWordRun v t).1).2) := by
  induction v generalizing t with
  | nil => simp [actualPrincipalWordRun]
  | cons p v ih =>
    rcases p with ⟨eta,c⟩
    simp [actualPrincipalWordRun,ih,Nat.add_assoc]

private theorem genuine_append (v w : List (ONote × Nat)) (t : Nat) :
    actualPrincipalWordGenuine (v++w) t ↔ actualPrincipalWordGenuine v t ∧
      actualPrincipalWordGenuine w (actualPrincipalWordRun v t).1 := by
  induction v generalizing t with
  | nil => simp [actualPrincipalWordGenuine,actualPrincipalWordRun]
  | cons p v ih =>
    rcases p with ⟨eta,c⟩
    simp [actualPrincipalWordGenuine,actualPrincipalWordRun,ih,and_assoc]

private theorem append_primitive : Primrec (fun p : Nat × Nat × Nat =>
    encodedComparisonAppendKernel p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have he : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp := Primrec.unpair.comp (Primrec.nat_div.comp hn (Primrec.const 2))
  have hw : Primrec (fun p : Nat × Nat × Nat =>
      (Encodable.decode (α := List (Nat × Nat)) (p.1/2).unpair.1).getD []) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp hp)) (Primrec.const [])
  have hnew := Primrec.list_append.comp hw
    (Primrec.list_cons.comp (he.pair hc) (Primrec.const []))
  exact Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec.encode.comp hnew) (Primrec.snd.comp hp)))

theorem primitive : Targets.SuccessorWordProgramsPrimitiveRecursive := by
  have hn : Primrec (fun p : Nat × Nat × Nat × Nat => p.1) := Primrec.fst
  have he : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hw := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp hd
  have hm := Primrec.nat_add.comp (Primrec.succ.comp hc) hw
  have hfirst := append_primitive.comp (hn.pair (he.pair hm))
  have hnew := append_primitive.comp (hfirst.pair (hd.pair hc))
  refine ⟨append_primitive,hnew,?_⟩
  have hold := append_primitive.comp (hn.pair (he.pair hc))
  exact Primrec.nat_max.comp (OneVariableComparison.source_program.1.comp hold)
    (OneVariableComparison.source_program.1.comp hnew)

private theorem append_source (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) (eta : NONote) (c : Nat) :
    encodedComparisonAppendKernel (oneVariableComparisonEncode (.range w E)) (rawNoteEncode eta.1) c=
      oneVariableComparisonEncode (.range (w++[(eta,c)]) E) := by
  let q := Nat.pair (Encodable.encode (encodePrincipalKernelWord (comparisonRawWord w))) (positiveExprEncode E)
  have hq : (2*q+1)/2=q := by omega
  change 2*Nat.pair (Encodable.encode
      (((Encodable.decode (α := List (Nat × Nat)) ((2*q+1)/2).unpair.1).getD [])++[(rawNoteEncode eta.1,c)]))
        ((2*q+1)/2).unpair.2+1=_
  rw [hq]
  simp [q,oneVariableComparisonEncode,comparisonRawWord,encodePrincipalKernelWord,List.map_append]

theorem source : Targets.SuccessorWordProgramsSource := by
  intro w E eta pred c
  refine ⟨append_source w E eta c,?_⟩
  unfold encodedSuccessorWordExpansion
  rw [rawNormCodeCorrect pred.1,append_source,append_source]
  simp only [successorExpandedWord,List.append_assoc,List.singleton_append]

private theorem kernel_pair (eta pred : NONote) (c t : Nat) (hp : 0<pred.1.repr)
    (hs : eta.1.repr=pred.1.repr+1)
    (hd : c+1+Vendor.R1.treeWeight pred.1+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t) :
    actualPrincipalWordRun [(eta.1,c)] t=
      actualPrincipalWordRun [(eta.1,c+1+Vendor.R1.treeWeight pred.1),(pred.1,c)] t := by
  have hL : Ordinal.omega0^pred.1.repr*Ordinal.omega0=Ordinal.omega0^eta.1.repr := by
    rw [← Ordinal.opow_add_one,← hs]
  have he : Ordinal.omega0^pred.1.repr*Ordinal.omega0<epsilonZero := by
    rw [hL]
    exact principal_below eta
  have hdom : c+actualOrdinalNorm (Ordinal.omega0^pred.1.repr)+
      actualOrdinalNorm (Ordinal.omega0^pred.1.repr*Ordinal.omega0)≤t := by
    rw [hL,principal_norm]
    omega
  have hv := actualSuccessorKernelComposition pred.1.repr hp he c t hdom
  have hcount := actualSuccessorCountCocycle pred.1.repr hp he c t hdom
  rw [hL,principal_norm] at hv hcount
  apply Prod.ext
  · simpa [actualPrincipalWordRun,Nat.add_assoc] using hv
  · simpa [actualPrincipalWordRun,Nat.add_assoc] using hcount

theorem actual_program : Targets.ActualSuccessorWordProgram := by
  refine ⟨primitive,?_⟩
  intro w E eta pred c hv hp hs
  have hnew : oneVariableComparisonValid (.range (successorExpandedWord w eta pred c) E) := by
    refine ⟨?_,?_,hv.2.2.1,hv.2.2.2⟩
    · simp [successorExpandedWord]
    · intro p hmem
      simp only [successorExpandedWord,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hw | h1 | h2
      · exact hv.2.1 p (List.mem_append_left _ hw)
      · subst p
        rw [hs]
        exact hp.trans (lt_add_one _)
      · subst p
        exact hp
  refine ⟨hnew,?_⟩
  intro x hx
  have hsource := source w E eta pred c
  have hmax : max (oneVariableComparisonDomainBound (.range (w++[(eta,c)]) E))
      (oneVariableComparisonDomainBound (.range (successorExpandedWord w eta pred c) E))≤x := by
    unfold encodedSuccessorWordTail at hx
    rw [hsource.1,hsource.2,
      (OneVariableComparison.source_program.2.2 _ hv).1,
      (OneVariableComparison.source_program.2.2 _ hnew).1] at hx
    exact hx
  have hold := ((OneVariableComparison.source_program.2.2 _ hv).2.2 x ((Nat.le_max_left _ _).trans hmax)).1
  have hout := ((OneVariableComparison.source_program.2.2 _ hnew).2.2 x ((Nat.le_max_right _ _).trans hmax)).1
  refine ⟨hold,hout,?_⟩
  have hg : actualPrincipalWordGenuine (comparisonRawWord w++
      [(eta.1,c+1+Vendor.R1.treeWeight pred.1),(pred.1,c)]) (actualFixedLimitProfileEval E x) := by
    simpa [oneVariableComparisonDomainAt,successorExpandedWord,comparisonRawWord,List.map_append] using hout
  have hd := (genuine_append _ _ _).mp hg
  have hpair := kernel_pair eta pred c
    (actualPrincipalWordRun (comparisonRawWord w) (actualFixedLimitProfileEval E x)).1 hp hs hd.2.1
  have hrawold : comparisonRawWord (w++[(eta,c)])=comparisonRawWord w++[(eta.1,c)] := by
    simp [comparisonRawWord]
  have hrawnew : comparisonRawWord (successorExpandedWord w eta pred c)=comparisonRawWord w++
      [(eta.1,c+1+Vendor.R1.treeWeight pred.1),(pred.1,c)] := by
    simp [comparisonRawWord,successorExpandedWord]
  rw [hrawold,hrawnew,word_append,word_append,hpair]

end LogicLineages.OrdinalComparison.SuccessorWordProgram
