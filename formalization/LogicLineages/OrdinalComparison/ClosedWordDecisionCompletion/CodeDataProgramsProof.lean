module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchTargets
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.CodeProgramsProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidueProgramsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmBaseProgramsProof
public import Mathlib.Data.List.Dedup

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodePrograms
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion
open LayeredComparison.SnyatkovCompletion
attribute [local irreducible] Nat.sqrt Nat.unpair
attribute [local irreducible] WordLinearDecisionCompletion.Code.decodeAtom

/-- All source occurrences are parsed before the actual raw-name deduplication. -/
theorem variables_primitive : Primrec Code.variables := by
  let Item := Int × (Nat × Word)
  have hd := WordLinearDecisionCompletion.Proof.decodeAtom_primitive
  have hitems : Primrec (fun payload : Nat =>
      (WordLinearDecisionCompletion.Code.decodeAtom payload).2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hd))
  have hname : Primrec (fun p : Nat × Item => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun payload : Nat =>
      rowVariables (WordLinearDecisionCompletion.Code.decodeAtom payload).2.2) :=
    Primrec.list_map hitems hname.to₂
  exact Primrec.list_flatMap LinearRowsCodeProof.atoms_primitive (hr.comp Primrec.snd).to₂

/-- A literal fold implementation of the actual Nat-name deduplication. -/
theorem dedup_primitive : Primrec (fun xs : List Nat => xs.dedup) := by
  have hm : PrimrecPred (fun p : Nat × List Nat => p.1 ∈ p.2) :=
    (Primrec.nat_lt.comp Primrec.list_idxOf
      (Primrec.list_length.comp Primrec.snd)).of_eq
        (fun _ => List.idxOf_lt_length_iff)
  have hs : Primrec₂ (fun (_ : List Nat) => fun p : Nat × List Nat =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2) :=
    (Primrec.ite (hm.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂
  apply (Primrec.list_foldr Primrec.id (Primrec.const ([] : List Nat)) hs).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [id_eq,List.foldr_cons] at ih ⊢
      rw [ih,List.dedup_cons']

theorem names_primitive : Primrec Code.names :=
  dedup_primitive.comp variables_primitive

theorem residueAtom_primitive : Primrec Code.residueAtom := by
  let A := WordLinearDecisionCompletion.Code.AtomData
  have hm : Primrec (fun a : A => a.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun a : A => a.2.2) := Primrec.snd.comp Primrec.snd
  have hrow : Primrec (fun a : A => WordResidue.row (a.2.1+1) a.2.2) :=
    WordResidue.Proof.rowPrimitive.comp ((Primrec.succ.comp hm).pair hr)
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.id
    (Primrec.fst.pair (hm.pair hrow))

theorem residue_primitive : Primrec Code.residue := by
  have hop : Primrec₂ (fun (_ : Nat) payload => Encodable.encode
      (Code.residueAtom (WordLinearDecisionCompletion.Code.decodeAtom payload))) :=
    Primrec.encode.comp (residueAtom_primitive.comp
      (WordLinearDecisionCompletion.Proof.decodeAtom_primitive.comp Primrec.snd))
  exact (LinearRowsCodeProof.mapAtoms_primitive hop).comp (Primrec.const 0) Primrec.id

theorem residueTail_primitive : Primrec Code.residueTail := by
  have hd := WordLinearDecisionCompletion.Proof.decodeAtom_primitive
  have hm : Primrec (fun payload : Nat =>
      (WordLinearDecisionCompletion.Code.decodeAtom payload).2.1+1) :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp hd))
  have hr : Primrec (fun payload : Nat =>
      (WordLinearDecisionCompletion.Code.decodeAtom payload).2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hd)
  have ht : Primrec (fun payload : Nat =>
      let a := WordLinearDecisionCompletion.Code.decodeAtom payload
      if a.1 = 0 then 0 else WordResidue.rowTail (a.2.1+1) a.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hd) (Primrec.const 0))
      (Primrec.const 0) (WordResidue.Proof.rowTailPrimitive.comp (hm.pair hr))
  exact AlgorithmPrograms.foldMax_primitive.comp
    (Primrec.list_map LinearRowsCodeProof.atoms_primitive (ht.comp Primrec.snd).to₂)

#print axioms variables_primitive
#print axioms dedup_primitive
#print axioms names_primitive
#print axioms residueAtom_primitive
#print axioms residue_primitive
#print axioms residueTail_primitive

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodePrograms
