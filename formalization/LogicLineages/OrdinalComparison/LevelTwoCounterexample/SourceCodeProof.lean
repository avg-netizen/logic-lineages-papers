module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceTargets
import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarCodeProof
import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairCodeProof
import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitProof
import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveProof
import LogicLineages.OrdinalComparison.WWSourceComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceCodeProof
open Source Source.ForwardTranslation SourceCode

private theorem bool_and_primitive : Primrec₂ Bool.and := by
  apply (Primrec.cond Primrec.fst Primrec.snd (Primrec.const false)).of_eq
  intro p
  cases p.1 <;> rfl

theorem positiveFlag_primitive :
    Primrec (fun p : Nat × EncodedVector × EncodedVector => positiveFlag p.1 p.2.1 p.2.2) := by
  let A := Nat × EncodedVector × EncodedVector
  have hn : Primrec (fun v : EncodedVector => v.2.map encodedClosedPositive) :=
    Primrec.list_map Primrec.snd (encodedClosedPositivePrimitiveRecursive.comp Primrec.snd)
  have ha : Primrec (fun p : A => p.2.1.2.map encodedClosedPositive) := hn.comp (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : A => p.2.2.2.map encodedClosedPositive) := hn.comp (Primrec.snd.comp Primrec.snd)
  have hab := positiveComparisonPrimitiveRecursive.comp ha hb
  have hba := positiveComparisonPrimitiveRecursive.comp hb ha
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) hab
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) hab (bool_and_primitive.comp hab hba))

theorem actualNumericProgram : SourceTargets.ActualNumericProgram := by
  have ha : Primrec (fun p : Input => GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.1)) :=
    GroundPositiveQuerySplit.Proof.vectorAt_primitive.comp
      (Primrec.fst.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hb : Primrec (fun p : Input => GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.2)) :=
    GroundPositiveQuerySplit.Proof.vectorAt_primitive.comp
      (Primrec.fst.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  let A := (Input × EncodedVector) × EncodedVector
  have hp : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun p : A => p.1.1.1) := Primrec.fst.comp hp
  have hm : Primrec (fun p : A => p.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp hp)
  have hav : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hbv : Primrec (fun p : A => p.2) := Primrec.snd
  have hf := positiveFlag_primitive.comp (hm.pair (hav.pair hbv))
  have hla := ScalarCodeProof.actualNumericPrograms.2.1.comp (Primrec.fst.comp hav)
  have hlb := ScalarCodeProof.actualNumericPrograms.2.1.comp (Primrec.fst.comp hbv)
  have hout := PairCodeProof.actualNumericProgram.comp (hn.pair (hm.pair (hf.pair (hla.pair hlb))))
  exact Primrec.option_bind ha
    (Primrec.option_bind (hb.comp Primrec.fst) (Primrec.option_some.comp hout).to₂).to₂
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceCodeProof
