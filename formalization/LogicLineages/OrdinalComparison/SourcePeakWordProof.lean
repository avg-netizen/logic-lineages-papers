module
public import LogicLineages.OrdinalComparison.SourcePeakWordTargets
public import LogicLineages.OrdinalComparison.PeakWordProgramWordProof
public import LogicLineages.OrdinalComparison.PeakWordProof
public import LogicLineages.OrdinalComparison.CollectedNormalizeProof
public import LogicLineages.OrdinalComparison.ComparisonSignatureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourcePeakWord

private theorem blocks_erasure (rho : NONote) :
    (comparisonTypedPrincipalBlocks rho).map Subtype.val=principalExponentBlocks rho.1 := by
  unfold comparisonTypedPrincipalBlocks
  exact (List.map_map (β := NONote) (g := fun e : NONote => e.1)
    (f := fun e : {e : ONote // e∈principalExponentBlocks rho.1} =>
      (⟨e.1,(actualPrincipalBlocksNormalOrder rho.1 rho.2).1 e.1 e.2⟩ : NONote))).trans
        (List.attach_map_subtype_val _)

private theorem word_erasure (es : List NONote) (c : Nat) :
    comparisonRawWord (comparisonTypedPrincipalWord es c)=principalKernelWord (es.map Subtype.val) c := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
    change comparisonRawWord (comparisonTypedPrincipalWord es (c+(1+Vendor.R1.treeWeight e.1))++[(e,c)])=
      principalKernelWord (e.1::es.map Subtype.val) c
    rw [principalKernelWord]
    unfold comparisonRawWord
    rw [List.map_append (f := fun p : NONote × Nat => (p.1.1,p.2))]
    change comparisonRawWord (comparisonTypedPrincipalWord es (c+(1+Vendor.R1.treeWeight e.1)))++[(e.1,c)]=_
    rw [ih]

private theorem source_erasure (rho : NONote) :
    comparisonRawWord (comparisonTypedPrincipalWord (comparisonTypedPrincipalBlocks rho) 0)=
      principalKernelWord (principalExponentBlocks rho.1) 0 := by
  rw [word_erasure,blocks_erasure]

theorem shape : Targets.SourcePeakWordLiteralShape := by
  refine ⟨blocks_erasure,word_erasure,?_⟩
  intro rho E
  simp [comparisonLiteralSourceHeadCount,comparisonSourcePeakWord,comparisonPositiveSourceHeadCount]

theorem program : Targets.SourcePeakWordCodeProgram := by
  have hr : Primrec (fun p : Nat × Nat => p.1) := Primrec.fst
  have ha : Primrec (fun p : Nat × Nat => p.2) := Primrec.snd
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hw := Primrec.encode.comp (PeakWordProgram.peak.1.comp hr)
  have he := Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp ha
      (Primrec.nat_mul.comp (Primrec.const 4) (hn.comp hr)))) (Primrec.const 2)
  refine ⟨Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp hw he)),?_⟩
  intro rho E
  simp only [encodedSourcePeakWord,PeakWordProgram.peak.2 rho.1,rawNormCodeCorrect rho.1,
    comparisonSourcePeakWord,oneVariableComparisonEncode,positiveExprEncode,source_erasure]

private theorem word_member (es : List NONote) (c : Nat) :
    ∀ p∈comparisonTypedPrincipalWord es c,p.1∈es := by
  induction es generalizing c with
  | nil => intro p hp; cases hp
  | cons e es ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact List.mem_cons_of_mem e (ih _ p hp)
    · have heq : p=(e,c) := List.mem_singleton.mp hp
      subst p
      exact List.mem_cons_self

theorem carrier : Targets.SourcePeakWordFiniteCarrier := by
  intro budget rho hbound p hp
  have hm := word_member (comparisonTypedPrincipalBlocks rho) 0 p hp
  have he : p.1.1∈principalExponentBlocks rho.1 := by
    rw [←blocks_erasure rho]
    exact List.mem_map.mpr ⟨p.1,hm,rfl⟩
  exact ⟨hm,ComparisonSignature.principal_coverage budget rho hbound p.1.1 he⟩

theorem semantics : Targets.ActualSourcePeakWordSemantics := by
  intro rho hl _ E hv hopen
  have hw : comparisonTypedPrincipalWord (comparisonTypedPrincipalBlocks rho) 0≠[] := by
    intro hz
    have hr := source_erasure rho
    rw [hz] at hr
    exact (fullActualPrincipalPeakWord rho hl 0).1 hr.symm
  have hpos : ∀ p∈comparisonTypedPrincipalWord (comparisonTypedPrincipalBlocks rho) 0,0<p.1.1.repr := by
    intro p hp
    have hm := word_member (comparisonTypedPrincipalBlocks rho) 0 p hp
    have he : p.1.1∈principalExponentBlocks rho.1 := by
      rw [←blocks_erasure rho]
      exact List.mem_map.mpr ⟨p.1,hm,rfl⟩
    exact (actualPrincipalBlocksLimitDomain rho.1 rho.2 hl).2 p.1.1 he
  refine ⟨⟨hw,hpos,⟨hv,True.intro⟩,?_⟩,?_⟩
  · simpa only [positiveExprHasInput,Bool.or_false] using hopen
  · intro x
    have hpeak := fullActualPrincipalPeakWord rho hl (actualFixedLimitProfileEval E x)
    refine ⟨?_,?_,?_,?_⟩
    · change actualPrincipalWordGenuine _ (actualFixedLimitProfileEval E x+Vendor.R1.treeWeight rho.1)
      rw [source_erasure,Nat.add_comm]
      exact hpeak.2.2.1
    · change (actualPrincipalWordRun _ (actualFixedLimitProfileEval E x+Vendor.R1.treeWeight rho.1)).1=_
      rw [source_erasure,Nat.add_comm,hpeak.2.1]
      simp only [actualCollectedTagPeak,actualCollectedTagInput,collectedPositiveNormalizeValue E hv x]
    · simpa only [source_erasure] using hpeak.2.2.2.1
    · simpa only [source_erasure] using hpeak.2.2.2.2

theorem full : Targets.FullActualSourcePeakWord := ⟨program,shape,semantics,carrier⟩

end LogicLineages.OrdinalComparison.SourcePeakWord
