module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPartitionProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

theorem partitionTail_computable {α : Type} [Primcodable α]
    (D maximum : α → Nat) (r : α → Row) (hD : Computable D)
    (hmaximum : Computable maximum) (hr : Computable r) :
    Computable (fun a => partitionTail (D a) (maximum a) (r a)) := by
  have hactive := active_primitive.to_comp.comp hr
  have hp := comparisonCutoff_computable
    (fun p : (α × Item) × Item => D p.1.1)
    (fun p => maximum p.1.1) (fun p => leader p.1.2) (fun p => leader p.2)
    (hD.comp (Computable.fst.comp Computable.fst))
    (hmaximum.comp (Computable.fst.comp Computable.fst))
    (leader_primitive.to_comp.comp (Computable.snd.comp Computable.fst))
    (leader_primitive.to_comp.comp Computable.snd)
  have hi := computable_map ((0 : Int),0,([] : Word)) (hactive.comp Computable.fst) hp.to₂
  have hflat : Computable (fun a => (active (r a)).flatMap (fun x =>
      (active (r a)).map (fun y => comparisonCutoff (D a) (maximum a) (leader x) (leader y)))) :=
    Primrec.list_flatten.to_comp.comp (computable_map ((0 : Int),0,([] : Word)) hactive hi.to₂)
  exact Primrec.nat_max.to_comp.comp (rowSourceTail_primitive.to_comp.comp hr)
    (foldMax_primitive.to_comp.comp hflat)

theorem partitionGuard_encode_computable {α : Type} [Primcodable α]
    (D maximum : α → Nat) (r : α → Row) (labels : α → List Nat)
    (hD : Computable D) (hmaximum : Computable maximum) (hr : Computable r)
    (hl : Computable labels) :
    Computable (fun a => Formula.encode (partitionGuard (D a) (maximum a) (r a) (labels a))) := by
  have hz := labelled_primitive.to_comp.comp hr hl
  have hs : Computable (fun p : (α × Labelled) × Labelled =>
      FullWordGuardCompletion.orderNat p.1.2.2 p.2.2) :=
    FullWordGuardCompletion.ComparisonProgramsProof.orderNat_primitive.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) (Computable.snd.comp Computable.snd)
  have hp := comparisonGuard_encode_computable
    (fun p : (α × Labelled) × Labelled => D p.1.1) (fun p => maximum p.1.1)
    (fun p => leader p.1.2.1) (fun p => leader p.2.1)
    (fun p => FullWordGuardCompletion.orderNat p.1.2.2 p.2.2)
    (hD.comp (Computable.fst.comp Computable.fst))
    (hmaximum.comp (Computable.fst.comp Computable.fst))
    (leader_primitive.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst)))
    (leader_primitive.to_comp.comp (Computable.fst.comp Computable.snd)) hs
  have hi := computable_map (((0 : Int),0,([] : Word)),0) (hz.comp Computable.fst) hp.to₂
  have hflat : Computable (fun a => (labelled (r a) (labels a)).flatMap (fun x =>
      (labelled (r a) (labels a)).map (fun y => Formula.encode
        (comparisonGuard (D a) (maximum a) (leader x.1) (leader y.1)
          (FullWordGuardCompletion.orderNat x.2 y.2))))) :=
    Primrec.list_flatten.to_comp.comp
      (computable_map (((0 : Int),0,([] : Word)),0) hz hi.to₂)
  apply (conjunctionCodes_primitive.to_comp.comp hflat).of_eq
  intro a
  simp only [partitionGuard,conjoin_encode,List.map_flatMap,List.map_map,Function.comp_def]

theorem lastClass_primitive : Primrec (fun xs : List (List Item) => xs.getLastD []) := by
  apply (Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.list_reverse)
    (Primrec.const ([] : List Item))).of_eq
  intro xs
  simp

theorem partitionBranch_encode_computable {α : Type} [Primcodable α]
    (D maximum : α → Nat) (r : α → Row) (labels : α → List Nat)
    (hD : Computable D) (hmaximum : Computable maximum) (hr : Computable r)
    (hl : Computable labels) :
    Computable (fun a => encodeBranch (partitionBranch (D a) (maximum a) (r a) (labels a))) := by
  have hp := partitionTail_computable D maximum r hD hmaximum hr
  have hg := partitionGuard_encode_computable D maximum r labels hD hmaximum hr hl
  have hz := zeroClass_primitive.to_comp.comp hr hl
  have hclasses := classes_primitive.to_comp.comp hr hl
  have hleading := leading_primitive.to_comp.comp (lastClass_primitive.to_comp.comp hclasses)
  have hlt : Computable (fun p : Int × Int => decide (p.1 < p.2)) :=
    FullWordGuardCompletion.ComparisonProgramsProof.int_lt_primitive.to_comp
  have hsign : Computable (fun a => if leading ((classes (r a) (labels a)).getLastD []) < 0
      then (0 : Nat) else 2) := by
    apply (Computable.cond (hlt.comp (hleading.pair (Computable.const (0 : Int))))
      (Computable.const 0) (Computable.const 2)).of_eq
    intro a
    by_cases h : leading ((classes (r a) (labels a)).getLastD []) < 0 <;> simp [h,Bool.cond_eq_ite]
  have hnone := (Primrec.nat_max.to_comp.comp hp (signTail_primitive.to_comp.comp hr)).pair
    (hg.pair ((Computable.const 0).pair (hsign.pair (Computable.const ((0,[]) : Row)))))
  have hrow := rewrite_primitive.to_comp.comp ((hD.comp Computable.fst).pair
    ((hr.comp Computable.fst).pair ((hl.comp Computable.fst).pair Computable.snd)))
  have hsome : Computable₂ (fun a removed =>
      ((partitionTail (D a) (maximum a) (r a),Formula.encode
        (partitionGuard (D a) (maximum a) (r a) (labels a)),
        (1,(0,rewrite (D a) (r a) (labels a) removed))) : EncodedBranch)) :=
    ((hp.comp Computable.fst).pair ((hg.comp Computable.fst).pair
      ((Computable.const 1).pair ((Computable.const 0).pair hrow)))).to₂
  apply (Computable.option_casesOn hz hnone hsome).of_eq
  intro a
  cases h : zeroClass (r a) (labels a) <;> simp [partitionBranch,h,encodeBranch]

theorem encodeBranch_updateTail (b : Branch) (paid : Nat) :
    encodeBranch {b with tail := max paid b.tail} = (max paid (encodeBranch b).1,(encodeBranch b).2) := by
  cases b with
  | mk tail guard action => cases action <;> rfl

theorem actualStageProgram : AlgorithmTargets.ActualStageProgram := by
  let A := Nat × Nat × Row
  have hD : Computable (fun p : A => p.1) := Computable.fst
  have hm : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hr : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have hc := canonicalRow_primitive.to_comp.comp hr
  have htail := rowTail_primitive.to_comp.comp hr
  have hmaximum := hasMaximum_primitive.to_comp.comp hm hc
  have hn := Computable.list_length.comp (active_primitive.to_comp.comp hc)
  have hassignment := assignments_primitive.to_comp.comp hn hn
  have hb := partitionBranch_encode_computable
    (fun p : A × List Nat => p.1.1) (fun p => p.1.2.1)
    (fun p => canonicalRow p.1.2.2) Prod.snd
    (hD.comp Computable.fst) (hm.comp Computable.fst) (hc.comp Computable.fst) Computable.snd
  have hadjusted : Computable (fun p : A × List Nat =>
      encodeBranch {partitionBranch p.1.1 p.1.2.1 (canonicalRow p.1.2.2) p.2 with
        tail := max (rowTail p.1.2.2)
          (partitionBranch p.1.1 p.1.2.1 (canonicalRow p.1.2.2) p.2).tail}) := by
    apply ((Primrec.nat_max.to_comp.comp (htail.comp Computable.fst)
      (Computable.fst.comp hb)).pair (Computable.snd.comp hb)).of_eq
    intro p
    exact (encodeBranch_updateTail _ _).symm
  have hall := computable_map ([] : List Nat) hassignment hadjusted.to₂
  have hlinearEntry := (Primrec.nat_max.to_comp.comp htail (rowSourceTail_primitive.to_comp.comp hc)).pair
    ((Computable.const 0).pair ((Computable.const 0).pair ((Computable.const 3).pair hc)))
  have hlinear := Computable.list_cons.comp hlinearEntry (Computable.const ([] : List EncodedBranch))
  apply (Computable.cond hmaximum hall hlinear).of_eq
  intro p
  cases h : hasMaximum p.2.1 (canonicalRow p.2.2) <;>
    simp [stage,h,Bool.cond_eq_ite,List.map_map,Function.comp_def,encodeBranch,Formula.encode]

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
