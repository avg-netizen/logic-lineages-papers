module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeGraphSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsAssemblyProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem graphChildren_computable : Computable graphChildren := by
  have hq : Primrec (fun p : GraphCall => p.2 / 10) := quotient_primitive.comp Primrec.snd
  have hl : Primrec (fun p : GraphCall => (p.2 / 10).unpair.1) := left_primitive.comp Primrec.snd
  have hr : Primrec (fun p : GraphCall => (p.2 / 10).unpair.2) := right_primitive.comp Primrec.snd
  have hs : Computable (fun p : GraphCall => p.1 + nodeCount (p.2 / 10).unpair.1) :=
    Primrec.nat_add.to_comp.comp Computable.fst (nodeCount_computable.comp hl.to_comp)
  unfold graphChildren
  exact ComputableMapAtomsProof.computable_ite (((tag_is 0).or (tag_is 1)).comp Primrec.snd)
    (Computable.const [])
    (ComputableMapAtomsProof.computable_ite (((tag_is 2).or (tag_is 3)).comp Primrec.snd)
      (Computable.list_cons.comp (Computable.fst.pair hl.to_comp)
        (Computable.list_cons.comp (hs.pair hr.to_comp) (Computable.const [])))
      (ComputableMapAtomsProof.computable_ite (((tag_is 4).or (tag_is 5)).comp Primrec.snd)
        (Computable.list_cons.comp (Computable.fst.pair hr.to_comp) (Computable.const []))
        (ComputableMapAtomsProof.computable_ite (((tag_is 6).or (tag_is 8)).comp Primrec.snd)
          (Computable.list_cons.comp (Computable.fst.pair hq.to_comp) (Computable.const []))
          (Computable.const []))))
#print axioms graphChildren_computable


end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
