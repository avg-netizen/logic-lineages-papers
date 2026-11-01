module
public import LogicLineages.OrdinalComparison.ComparisonExpansionTargets
public import LogicLineages.OrdinalComparison.SourceKernelCallsProof
public import LogicLineages.OrdinalComparison.SourcePeakWordProof
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsProgramProof
public import LogicLineages.OrdinalComparison.ComparisonSourceDomainProgramProof
public import LogicLineages.OrdinalComparison.SuccessorNormalizationProgramProof
public import LogicLineages.OrdinalComparison.RawComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonExpansion

theorem word_primitive : Primrec encodedComparisonWord := by
  have hp := Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  exact Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp hp)) (Primrec.const [])

theorem outer_primitive : Primrec encodedComparisonOuter := by
  have h := (Primrec.list_getD ((0,0) : Nat × Nat)).comp
    (Primrec.list_reverse.comp word_primitive) (Primrec.const 0)
  exact h.of_eq (by intro n; unfold encodedComparisonOuter; cases (encodedComparisonWord n).reverse <;> rfl)

theorem prefix_program : Targets.ComparisonRangePrefixProgram := by
  have hw := Primrec.list_reverse.comp (Primrec.list_tail.comp (Primrec.list_reverse.comp word_primitive))
  have ha := Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
  refine ⟨Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec.encode.comp hw) ha)),?_⟩
  intro w eta c E
  let word := encodePrincipalKernelWord (comparisonRawWord (w++[(eta,c)]))
  let q := Nat.pair (Encodable.encode word) (positiveExprEncode E)
  have hd : (2*q+1)/2=q := by omega
  change 2*Nat.pair (Encodable.encode
    (((Encodable.decode (α := List (Nat × Nat)) ((2*q+1)/2).unpair.1).getD []).reverse.tail.reverse))
      ((2*q+1)/2).unpair.2+1=_
  rw [hd]
  simp only [q,Nat.unpair_pair,Encodable.encodek,Option.getD_some]
  simp only [word,encodePrincipalKernelWord,comparisonRawWord,List.map_append,List.map_singleton,
    List.reverse_append,List.reverse_singleton,List.singleton_append,List.tail_cons,List.reverse_reverse]
  rfl

theorem positive_primitive : Primrec₂ encodedComparisonPositiveChildren := by
  have hh : Primrec (fun p : Nat × Nat => encodedDisplayedSourceHeads p.1++encodedDisplayedSourceHeads p.2) :=
    Primrec.list_append.comp (SourceDisplayedHeads.program.1.comp Primrec.fst)
      (SourceDisplayedHeads.program.1.comp Primrec.snd)
  have ha : Primrec (fun p : ((Nat × Nat) × (Nat × Nat)) × (Nat × Nat) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hb : Primrec (fun p : ((Nat × Nat) × (Nat × Nat)) × (Nat × Nat) => p.2) := Primrec.snd
  have hpa := SourcePeakWord.program.1.comp (Primrec.fst.comp ha) (Primrec.snd.comp ha)
  have hpb := SourcePeakWord.program.1.comp (Primrec.fst.comp hb) (Primrec.snd.comp hb)
  have hlocal : Primrec₂ (fun q : (Nat × Nat) × (Nat × Nat) => fun b : Nat × Nat =>
      if q.2=b then ([] : List (Nat × Nat)) else
        [(encodedSourcePeakWord q.2.1 q.2.2,encodedSourcePeakWord b.1 b.2)]) :=
    Primrec.ite (Primrec.eq.comp ha hb) (Primrec.const [])
      (Primrec.list_cons.comp (hpa.pair hpb) (Primrec.const []))
  have hinner : Primrec (fun q : (Nat × Nat) × (Nat × Nat) =>
      (encodedDisplayedSourceHeads q.1.1++encodedDisplayedSourceHeads q.1.2).flatMap
        (fun b => if q.2=b then [] else [(encodedSourcePeakWord q.2.1 q.2.2,encodedSourcePeakWord b.1 b.2)])) :=
    Primrec.list_flatMap (hh.comp Primrec.fst) hlocal
  exact Primrec.list_flatMap hh hinner.to₂

attribute [local irreducible] encodedSuccessorNormalization

theorem mixed_primitive : Primrec₂ encodedComparisonMixedChildren := by
  have hh : Primrec (fun p : Nat × Nat => encodedComparisonOuter p.1) := outer_primitive.comp Primrec.fst
  have hl : Primrec (fun p : Nat × Nat => encodedComparisonOuter p.2) := outer_primitive.comp Primrec.snd
  have hr : Primrec (fun p : Nat × Nat =>
      encodedSuccessorNormalization (encodedComparisonRangePrefix p.1)
        (encodedComparisonOuter p.1).1 (encodedComparisonOuter p.2).1 (encodedComparisonOuter p.1).2) :=
    SuccessorNormalization.primitive.2.2.comp ((prefix_program.1.comp Primrec.fst).pair
      ((Primrec.fst.comp hh).pair ((Primrec.fst.comp hl).pair (Primrec.snd.comp hh))))
  have hsource := Primrec.fst.comp hr
  have hlast := Primrec.fst.comp (Primrec.snd.comp hr)
  have hlow : Primrec (fun p : Nat × Nat => encodedComparisonStripOuter p.2) :=
    SourceKernelCalls.program.1.comp Primrec.snd
  have hstrip := SourceKernelCalls.program.1.comp hsource
  exact Primrec.ite (Primrec.eq.comp hlast (Primrec.fst.comp hl))
    (Primrec.list_cons.comp (hstrip.pair hlow) (Primrec.const []))
    (Primrec.list_cons.comp (hsource.pair hlow) (Primrec.const []))

theorem children_primitive : Primrec₂ encodedComparisonChildren := by
  have hn : Primrec (fun p : Nat × Nat => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat => p.2) := Primrec.snd
  have hdn := Primrec.nat_div.comp hn (Primrec.const 2)
  have hdm := Primrec.nat_div.comp hm (Primrec.const 2)
  have hbad := ((Primrec.eq.comp (ComparisonSourceDomain.primitive.comp hn) (Primrec.const 1)).not).or
    ((Primrec.eq.comp (ComparisonSourceDomain.primitive.comp hm) (Primrec.const 1)).not)
  have hnpos := Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 2)) (Primrec.const 0)
  have hmpos := Primrec.eq.comp (Primrec.nat_mod.comp hm (Primrec.const 2)) (Primrec.const 0)
  have hP : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => encodedSourcePeakWord p.2.1 p.2.2) :=
    SourcePeakWord.program.1.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hL : Primrec (fun p : Nat × Nat => (encodedDisplayedSourceHeads (p.1/2)).map
      (fun q => (p.2,encodedSourcePeakWord q.1 q.2))) :=
    Primrec.list_map (SourceDisplayedHeads.program.1.comp hdn)
      ((Primrec.snd.comp Primrec.fst).pair hP)
  have hR : Primrec (fun p : Nat × Nat => (encodedDisplayedSourceHeads (p.2/2)).map
      (fun q => (p.1,encodedSourcePeakWord q.1 q.2))) :=
    Primrec.list_map (SourceDisplayedHeads.program.1.comp hdm)
      ((Primrec.fst.comp Primrec.fst).pair hP)
  have hA := outer_primitive.comp hn
  have hB := outer_primitive.comp hm
  have hEq := Primrec.eq.comp (Primrec.fst.comp hA) (Primrec.fst.comp hB)
  have hGt := Primrec.eq.comp
    (rawComparisonPrimitiveRecursive.comp (Primrec.fst.comp hA) (Primrec.fst.comp hB)) (Primrec.const 2)
  have hSame := Primrec.list_cons.comp
    ((SourceKernelCalls.program.1.comp hn).pair (SourceKernelCalls.program.1.comp hm)) (Primrec.const [])
  exact Primrec.ite hbad (Primrec.const [])
    (Primrec.ite hnpos (Primrec.ite hmpos (positive_primitive.comp hdn hdm) hL)
      (Primrec.ite hmpos hR (Primrec.ite hEq hSame
        (Primrec.ite hGt mixed_primitive (mixed_primitive.comp hm hn)))))

theorem program : Targets.ComparisonExpansionProgram :=
  ⟨word_primitive,outer_primitive,positive_primitive,mixed_primitive,children_primitive⟩

end LogicLineages.OrdinalComparison.ComparisonExpansion
