module
public import LogicLineages.PermittedControl.MixedRankNamedResidueRowTargets
import LogicLineages.PermittedControl.MixedRankNamedResidueRowSyntaxCodeProof
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks
import LogicLineages.PermittedControl.RankResidueChoicesStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.MixedRankNamedResidueRow
open PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)
open MixedRankResidue (rankSupport rankSupportCode residueVector residueVectorCode)
open RankResidueChoices (Slot Digit Cell namedSlots choices)
open MixedNamedResidueRow (keep)
open StatementChecks (fixed_mixedRankResidueCodeExact fixed_rankResidueLayoutAndChoices)

private theorem toVectorPrimitive : Primrec toVector := by
  have entry : Primrec (fun p : Cell × Digit => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_map Primrec.id entry.to₂

private abbrev Fold := RawArgs × (Cell × Nat)

private theorem rowStepPrimitive : Primrec₂ (fun (p : RawArgs) (z : Cell × Nat) =>
    if keep p.1 (p.2.1 + residueVectorCode p.2.2 (toVector z.1)) then
      6 * Nat.pair (clauseCode p.1 z.1) z.2 + 5 else z.2) := by
  have params : Primrec (Prod.fst : Fold → RawArgs) := Primrec.fst
  have state : Primrec (Prod.snd : Fold → Cell × Nat) := Primrec.snd
  have m : Primrec (fun p : Fold => p.1.1) := Primrec.fst.comp params
  have c : Primrec (fun p : Fold => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp params)
  have term : Primrec (fun p : Fold => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp params)
  have cell : Primrec (fun p : Fold => p.2.1) := Primrec.fst.comp state
  have tail : Primrec (fun p : Fold => p.2.2) := Primrec.snd.comp state
  have sum := add_primitive.comp c (fixed_mixedRankResidueCodeExact.2.1.comp term
    (toVectorPrimitive.comp cell))
  have selected : PrimrecPred (fun p : Fold => keep p.1.1 (p.1.2.1 +
      residueVectorCode p.1.2.2 (toVector p.2.1)) = true) := by
    simpa only [keep,decide_eq_true_eq] using
      Primrec.eq.comp (Primrec.nat_mod.comp (abs_primitive.comp sum) m) (Primrec.const 0)
  have disjunction := Primrec₂.natPair.comp (clauseCodePrimitive.comp m cell) tail
  have next := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) disjunction) (Primrec.const 5)
  exact Primrec.ite selected next tail

private theorem slotsPrimitive : Primrec (fun p : RawArgs => namedSlots (rankSupportCode p.2.2)) :=
  fixed_rankResidueLayoutAndChoices.1.comp (fixed_mixedRankResidueCodeExact.1.comp
    (Primrec.snd.comp Primrec.snd))

private theorem rowPrimitive : Primrec (fun p : RawArgs => rowCode p.1 p.2.1 p.2.2) := by
  have m : Primrec (fun p : RawArgs => p.1) := Primrec.fst
  have cells := fixed_rankResidueLayoutAndChoices.2.1.comp m slotsPrimitive
  exact Primrec.list_foldr cells (Primrec.const 1) rowStepPrimitive

private theorem preparePrimitive : Primrec prepareCode := by
  have m : Primrec (fun p : RawArgs => p.1) := Primrec.fst
  have entry : Primrec (fun s : Slot => ((s.1,(0,s.2,(0,0,0,0))) : NamedCode)) :=
    Primrec.fst.pair ((Primrec.const 0).pair (Primrec.snd.pair (Primrec.const (0,0,0,0))))
  have packet : Primrec (fun p : RawArgs => (namedSlots (rankSupportCode p.2.2)).map
      (fun s => ((s.1,(0,s.2,(0,0,0,0))) : NamedCode))) :=
    Primrec.list_map slotsPrimitive (entry.comp Primrec.snd).to₂
  exact Primrec.ite (Primrec.eq.comp m (Primrec.const 0)) (Primrec.const none)
    (Primrec.option_some.comp (packet.pair rowPrimitive))

private theorem rowLiteral (m : Nat) (c : Int) (terms : List WeightedOperand) :
    rowCode m c (terms.map encodeWeighted) = (row m c terms).encode := by
  unfold rowCode row rowFrom slots
  rw [fixed_mixedRankResidueCodeExact.2.2.1]
  generalize choices m (namedSlots (rankSupport terms)) = cells
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
    simp only [List.foldr_cons,fixed_mixedRankResidueCodeExact.2.2.2]
    by_cases selected : keep m (c + residueVector terms (toVector cell)) = true
    · simp only [if_pos selected,NormalForm.Formula.encode,clauseCodeLiteral,ih]
    · simp only [if_neg selected,ih]

theorem codeExact : CodeExact := by
  refine ⟨preparePrimitive,?_,?_⟩
  · rintro ⟨m,c,terms⟩ zero
    change m = 0 at zero
    simp [prepareCode,zero]
  · intro m c terms positive
    simp only [prepareCode,rawArgs,if_neg (Nat.ne_of_gt positive)]
    rw [fixed_mixedRankResidueCodeExact.2.2.1,rowLiteral]
    simp [requests,slots,List.map_map,Function.comp_def,encodeRequest,LowerOperand.code]

end LogicLineages.PermittedControl.MixedRankNamedResidueRow
