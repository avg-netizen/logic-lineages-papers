module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportBindProgramsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCompilerProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportPrograms
open PolynomialGraphCompletion WordLinearDecisionCompletion OutcomeTransport
open LayeredComparison.SnyatkovCompletion
attribute [local irreducible] Nat.sqrt Nat.unpair Computable Partrec

theorem decodeAtom_primitive : Primrec WordLinearDecisionCompletion.Code.decodeAtom :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat =>
      (Encodable.decode n : Option WordLinearDecisionCompletion.Code.AtomData)))
    (Primrec.const (0,0,(0 : Int),[]))

private theorem inequalityRows_fold (xs : List Nat) :
    xs.foldr (fun payload rest =>
      let a := WordLinearDecisionCompletion.Code.decodeAtom payload
      if a.1 = 0 then a.2.2 :: rest else rest) [] =
    xs.filterMap (fun payload =>
      let a := WordLinearDecisionCompletion.Code.decodeAtom payload
      if a.1 = 0 then some a.2.2 else none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldr_cons, List.filterMap_cons]
      split_ifs <;> simp_all

theorem inequalityRows_primitive : Primrec Code.inequalityRows := by
  let A := Nat × (Nat × List Row)
  have ha : Primrec (fun p : A => WordLinearDecisionCompletion.Code.decodeAtom p.2.1) :=
    decodeAtom_primitive.comp (Primrec.fst.comp Primrec.snd)
  have htag := Primrec.fst.comp ha
  have hrow := Primrec.snd.comp (Primrec.snd.comp ha)
  have hrest : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hs : Primrec (fun p : A =>
      let a := WordLinearDecisionCompletion.Code.decodeAtom p.2.1
      if a.1 = 0 then a.2.2 :: p.2.2 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
      (Primrec.list_cons.comp hrow hrest) hrest
  have hf := Primrec.list_foldr LinearRowsCodeProof.atoms_primitive
    (Primrec.const ([] : List Row)) hs.to₂
  apply hf.of_eq
  intro code
  exact inequalityRows_fold (LinearRows.Code.atoms code)

theorem originalTail_primitive : Primrec Code.originalTail :=
  AlgorithmPrograms.foldMax_primitive.comp
    (Primrec.list_map LinearRowsCodeProof.atoms_primitive
      (AlgorithmPrograms.rowTail_primitive.comp
        (Primrec.snd.comp (Primrec.snd.comp (decodeAtom_primitive.comp Primrec.snd)))).to₂)

theorem makeTable_primitive : Primrec₂ makeTable := by
  let A := List Row × List OutcomeData
  have hz : Primrec (fun p : A => p.1.zip p.2) :=
    (LayeredComparison.CommonHeadCode.Program.zipWith_primitive Prod.mk Primrec₂.pair).comp
      Primrec.fst Primrec.snd
  have he : Primrec (fun p : A × (Row × OutcomeData) => (Encodable.encode p.2.1,p.2.2)) :=
    (Primrec.encode.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_map hz he.to₂

theorem lookup_primitive : Primrec₂ lookup := by
  let A := Nat × Table
  have hk : Primrec (fun p : A × ((Nat × OutcomeData) × OutcomeData) => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ho : Primrec (fun p : A × ((Nat × OutcomeData) × OutcomeData) => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hs : Primrec (fun p : A × ((Nat × OutcomeData) × OutcomeData) =>
      if p.2.1.1 = p.1.1 then p.2.1.2 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp hk (Primrec.fst.comp Primrec.fst)) ho
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun p : A => p.2.foldr
      (fun entry rest => if entry.1 = p.1 then entry.2 else rest) (0,(0,[]))) :=
    Primrec.list_foldr Primrec.snd (Primrec.const (0,(0,[]))) hs.to₂
  apply hf.to₂.of_eq
  intro key table
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨k,o⟩
      simp only [List.foldr_cons, lookup, ih]

theorem outcomeFormula_primitive : Primrec Code.outcomeFormula := by
  have hr : Primrec (fun p : OutcomeData =>
      ((0,0,p.2) : WordLinearDecisionCompletion.Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair Primrec.snd)
  have hrow : Primrec (fun p : OutcomeData =>
      6 * Encodable.encode ((0,0,p.2) : WordLinearDecisionCompletion.Code.AtomData) + 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp hr))
      (Primrec.const 2)
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 1)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0) hrow)

theorem atom_primitive : Primrec₂ Code.atom := by
  let A := Table × Nat
  have ha : Primrec (fun p : A => WordLinearDecisionCompletion.Code.decodeAtom p.2) :=
    decodeAtom_primitive.comp Primrec.snd
  have hkey : Primrec (fun p : A =>
      Encodable.encode (WordLinearDecisionCompletion.Code.decodeAtom p.2).2.2) :=
    Primrec.encode.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have ho : Primrec (fun p : A =>
      Code.outcomeFormula (lookup (Encodable.encode (WordLinearDecisionCompletion.Code.decodeAtom p.2).2.2) p.1)) := by
    exact outcomeFormula_primitive.comp (lookup_primitive.comp hkey Primrec.fst)
  have hc : Primrec (fun p : A => 6 * p.2 + 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.snd) (Primrec.const 2)
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp ha) (Primrec.const 0)) ho hc

theorem rewrite_primitive : Primrec₂ Code.rewrite := by
  have ht : Primrec (fun p : Nat × List OutcomeData =>
      makeTable (Code.inequalityRows p.1) p.2) :=
    makeTable_primitive.comp (inequalityRows_primitive.comp Primrec.fst) Primrec.snd
  exact (bind_primitive atom_primitive).comp ht Primrec.fst

theorem transform_primitive : Primrec₂ Code.transform := by
  let A := Nat × EncodedPackage
  let C := Nat × List OutcomeData
  have hi : Primrec (fun p : A × C =>
      6 * Nat.pair p.2.1 (Code.rewrite p.1.1 p.2.2) + 4) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
        (rewrite_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))))
      (Primrec.const 4)
  have hm := Primrec.list_map (Primrec.snd.comp Primrec.snd) hi.to₂
  exact (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
    (originalTail_primitive.comp Primrec.fst)).pair hm

theorem compile_computable : Computable (fun p : Nat × Nat × Nat =>
    Code.compile p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Nat
  have hc : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have hr := inequalityRows_primitive.to_comp.comp hc
  have hp : Computable (fun p : A =>
      encodePackage (Runner.compile p.1 p.2.1 (Code.inequalityRows p.2.2))) :=
    RunnerCode.actualFamilyProgram.comp
      (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair hr))
  exact transform_primitive.to_comp.comp hc hp

theorem actualNumericPrograms : OutcomeTransportTargets.ActualNumericPrograms :=
  ⟨inequalityRows_primitive.to_comp,transform_primitive.to_comp,compile_computable⟩

#print axioms decodeAtom_primitive
#print axioms inequalityRows_fold
#print axioms inequalityRows_primitive
#print axioms originalTail_primitive
#print axioms makeTable_primitive
#print axioms lookup_primitive
#print axioms outcomeFormula_primitive
#print axioms atom_primitive
#print axioms rewrite_primitive
#print axioms transform_primitive
#print axioms compile_computable
#print axioms actualNumericPrograms

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportPrograms
