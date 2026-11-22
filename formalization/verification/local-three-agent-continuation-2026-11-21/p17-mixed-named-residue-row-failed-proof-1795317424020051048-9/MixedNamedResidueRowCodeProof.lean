module
public import LogicLineages.PermittedControl.MixedNamedResidueRowTargets
import LogicLineages.PermittedControl.MixedSameRankResidueStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.MixedNamedResidueRow
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open CountCongruenceNamedRow (requests residueAtom residueAtomCode)
open MixedSameRankResidue (WeightedCode WeightedOperand encodeWeighted weightedResidue
  weightedResidueCode)
open StatementChecks (fixed_mixedSameRankResidueCodeExact)

private abbrev RowArgs := Nat × Int × List WeightedCode
private abbrev FoldArgs := RowArgs × (Nat × Nat)

private theorem atomPrimitive : Primrec₂ residueAtomCode := by
  let Args := Nat × Nat
  have modulus : Primrec (fun q : Args => 2*q.1-1) :=
    Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) (Primrec.const 1)
  have offset : Primrec (fun q : Args => -(q.2 : Int)) :=
    negate_primitive.comp (ofNat_primitive.comp Primrec.snd)
  have data : Primrec (fun q : Args =>
      ((1,2*q.1-1,-(q.2 : Int),[(1,(0,1,0,0))])) : NormalForm.Code.AtomData)) :=
    (Primrec.const 1).pair (modulus.pair (offset.pair (Primrec.const [(1,(0,1,0,0))])))
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec.encode.comp data)) (Primrec.const 2)

private theorem rowStepPrimitive :
    Primrec₂ (fun (p : RowArgs) (z : Nat × Nat) =>
      if keep p.1 (p.2.1 + weightedResidueCode p.2.2 z.1) then
        6 * Nat.pair (residueAtomCode p.1 z.1) z.2 + 5 else z.2) := by
  have params : Primrec (Prod.fst : FoldArgs → RowArgs) := Primrec.fst
  have pair : Primrec (Prod.snd : FoldArgs → Nat × Nat) := Primrec.snd
  have m : Primrec (fun p : FoldArgs => p.1.1) := Primrec.fst.comp params
  have c : Primrec (fun p : FoldArgs => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp params)
  have terms : Primrec (fun p : FoldArgs => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp params)
  have j : Primrec (fun p : FoldArgs => p.2.1) := Primrec.fst.comp pair
  have tail : Primrec (fun p : FoldArgs => p.2.2) := Primrec.snd.comp pair
  have sum := add_primitive.comp c (fixed_mixedSameRankResidueCodeExact.1.comp terms j)
  have test : PrimrecPred (fun p : FoldArgs =>
      keep p.1.1 (p.1.2.1 + weightedResidueCode p.1.2.2 p.2.1) = true) := by
    simpa only [keep,decide_eq_true_eq] using
      Primrec.eq.comp (Primrec.nat_mod.comp (abs_primitive.comp sum) m) (Primrec.const 0)
  have disj := Primrec₂.natPair.comp (atomPrimitive.comp m j) tail
  have extended := Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) disj) (Primrec.const 5)
  exact Primrec.ite test extended tail

private theorem rowPrimitive : Primrec (fun p : RowArgs => rowCode p.1 p.2.1 p.2.2) := by
  have m : Primrec (Prod.fst : RowArgs → Nat) := Primrec.fst
  have indices : Primrec (fun p : RowArgs => List.range (2*p.1)) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) m)
  exact (Primrec.list_foldr indices (Primrec.const 1) rowStepPrimitive).of_eq (fun _ => rfl)

private theorem preparePrimitive : Primrec prepareCode := by
  have m : Primrec (fun q : RawArgs => q.1) := Primrec.fst
  have rank : Primrec (fun q : RawArgs => q.2.1) := Primrec.fst.comp Primrec.snd
  have cs : Primrec (fun q : RawArgs => q.2.2) := Primrec.snd.comp Primrec.snd
  have row := rowPrimitive.comp (m.pair cs)
  have request : Primrec (fun q : RawArgs => ((1,(0,q.2.1,(0,0,0,0))) : NamedCode)) :=
    (Primrec.const 1).pair ((Primrec.const 0).pair (rank.pair (Primrec.const (0,0,0,0))))
  have requests := Primrec.list_cons.comp request (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp m (Primrec.const 0)) (Primrec.const none)
    (Primrec.option_some.comp (requests.pair row))

private theorem rowLiteral (m : Nat) (c : Int) (terms : List WeightedOperand) :
    rowCode m c (terms.map encodeWeighted) = (row m c terms).encode := by
  unfold rowCode row rowFrom
  generalize List.range (2*m) = indices
  induction indices with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldr_cons, fixed_mixedSameRankResidueCodeExact.2.2.1 terms j]
    by_cases h : keep m (c + weightedResidue terms j) = true
    · simp only [if_pos h, NormalForm.Formula.encode, ih] <;> rfl
    · simp only [if_neg h, ih]

theorem codeExact : CodeExact := by
  refine ⟨preparePrimitive, ?_, ?_⟩
  · rintro ⟨m,rank,c,terms⟩ h
    change m = 0 at h
    simp [prepareCode,h]
  · intro m rank c terms hm
    simp only [prepareCode, rawArgs, if_neg (Nat.ne_of_gt hm), requests,
      List.map_cons, List.map_nil, encodeRequest, LowerOperand.code]
    rw [rowLiteral] <;> rfl

end LogicLineages.PermittedControl.MixedNamedResidueRow
