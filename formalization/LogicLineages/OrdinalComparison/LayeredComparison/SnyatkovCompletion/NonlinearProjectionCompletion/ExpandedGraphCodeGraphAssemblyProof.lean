module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeGraphChildrenProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeClauseProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair
attribute [local irreducible] output multiplyRow subtraction division inverse
attribute [local irreducible] SourceTermGraph.Code.equation

theorem graphAssemble_computable : Computable₂ graphAssemble := by
  let C := GraphCall × List Nat
  have hs : Computable (fun p : C => p.1.1) := Computable.fst.comp Computable.fst
  have hc : Primrec (fun p : C => p.1.2) := Primrec.snd.comp Primrec.fst
  have hq : Primrec (fun p : C => p.1.2 / 10) := quotient_primitive.comp hc
  have hl : Primrec (fun p : C => (p.1.2 / 10).unpair.1) := left_primitive.comp hc
  have hr : Primrec (fun p : C => (p.1.2 / 10).unpair.2) := right_primitive.comp hc
  have h0 : Computable (fun p : C => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : C => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd (Computable.const 1)
  have hn : Computable (fun p : C => p.1.1 + nodeCount (p.1.2 / 10).unpair.1) :=
    Primrec.nat_add.to_comp.comp hs (nodeCount_computable.comp hl.to_comp)
  have hu : Computable (fun p : C => p.1.1 + nodeCount (p.1.2 / 10)) :=
    Primrec.nat_add.to_comp.comp hs (nodeCount_computable.comp hq.to_comp)
  have ho : Computable (fun p : C => output p.1.1 p.1.2) := output_computable.comp hs hc.to_comp
  have hol : Computable (fun p : C => output p.1.1 (p.1.2 / 10).unpair.1) :=
    output_computable.comp hs hl.to_comp
  have hor : Computable (fun p : C => output (p.1.1 + nodeCount (p.1.2 / 10).unpair.1)
      (p.1.2 / 10).unpair.2) := output_computable.comp hn hr.to_comp
  have hos : Computable (fun p : C => output p.1.1 (p.1.2 / 10).unpair.2) :=
    output_computable.comp hs hr.to_comp
  have hoq : Computable (fun p : C => output p.1.1 (p.1.2 / 10)) :=
    output_computable.comp hs hq.to_comp
  have hnum : Computable (fun p : C => SourceTermGraph.Code.equation
      (SourceTermGraph.Code.numeralRow p.1.1 (p.1.2 / 10))) :=
    SourceTermGraphCodeProof.equation_primitive.to_comp.comp
      (SourceTermGraphCodeProof.numeralRow_primitive.to_comp.comp hs hq.to_comp)
  have hvar : Computable (fun p : C => SourceTermGraph.Code.equation
      (SourceTermGraph.Code.variableRow p.1.1 (p.1.2 / 10))) :=
    SourceTermGraphCodeProof.equation_primitive.to_comp.comp
      (SourceTermGraphCodeProof.variableRow_primitive.to_comp.comp hs hq.to_comp)
  have hadd : Computable (fun p : C => SourceTermGraph.Code.conjunction (p.2.getD 0 0)
      (SourceTermGraph.Code.conjunction (p.2.getD 1 0)
        (SourceTermGraph.Code.equation (SourceTermGraph.Code.additionRow (output p.1.1 p.1.2)
          (output p.1.1 (p.1.2 / 10).unpair.1)
          (output (p.1.1 + nodeCount (p.1.2 / 10).unpair.1) (p.1.2 / 10).unpair.2))))) :=
    SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp h0
      (SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp h1
        (SourceTermGraphCodeProof.equation_primitive.to_comp.comp
          (SourceTermGraphCodeProof.additionRow_primitive.to_comp.comp (ho.pair (hol.pair hor)))))
  have hsub : Computable (fun p : C => SourceTermGraph.Code.conjunction (p.2.getD 0 0)
      (SourceTermGraph.Code.conjunction (p.2.getD 1 0)
        (subtraction (output p.1.1 p.1.2) (output p.1.1 (p.1.2 / 10).unpair.1)
          (output (p.1.1 + nodeCount (p.1.2 / 10).unpair.1) (p.1.2 / 10).unpair.2)))) :=
    SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp h0
      (SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp h1
        (subtraction_primitive.to_comp.comp (ho.pair (hol.pair hor))))
  have hmul : Computable (fun p : C => SourceTermGraph.Code.conjunction (p.2.getD 0 0)
      (SourceTermGraph.Code.equation (multiplyRow (output p.1.1 p.1.2)
        (output p.1.1 (p.1.2 / 10).unpair.2) (p.1.2 / 10).unpair.1))) :=
    SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp h0
      (SourceTermGraphCodeProof.equation_primitive.to_comp.comp
        (multiplyRow_primitive.to_comp.comp (ho.pair (hos.pair hl.to_comp))))
  have hdiv : Computable (fun p : C => SourceTermGraph.Code.conjunction (p.2.getD 0 0)
      (division (output p.1.1 p.1.2) (output p.1.1 (p.1.2 / 10).unpair.2)
        (p.1.2 / 10).unpair.1)) :=
    SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp h0
      (division_primitive.to_comp.comp (ho.pair (hos.pair hl.to_comp)))
  have hphi : Computable (fun p : C => SourceTermGraph.Code.conjunction (p.2.getD 0 0)
      (SourceTermGraph.Code.equation (SourceTermGraph.Code.phiRow (output p.1.1 p.1.2)
        (output p.1.1 (p.1.2 / 10))))) :=
    SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp h0
      (SourceTermGraphCodeProof.equation_primitive.to_comp.comp
        (SourceTermGraphCodeProof.phiRow_primitive.to_comp.comp ho hoq))
  have hinv : Computable (fun p : C => SourceTermGraph.Code.conjunction (p.2.getD 0 0)
      (inverse (p.1.1 + nodeCount (p.1.2 / 10)) (output p.1.1 p.1.2)
        (output p.1.1 (p.1.2 / 10)))) :=
    SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp h0
      (inverse_primitive.to_comp.comp (hu.pair (ho.pair hoq)))
  change Computable (fun p : C => graphAssemble p.1 p.2)
  unfold graphAssemble
  exact ComputableMapAtomsProof.computable_ite ((tag_is 0).comp hc) hnum
    (ComputableMapAtomsProof.computable_ite ((tag_is 1).comp hc) hvar
      (ComputableMapAtomsProof.computable_ite ((tag_is 2).comp hc) hadd
        (ComputableMapAtomsProof.computable_ite ((tag_is 3).comp hc) hsub
          (ComputableMapAtomsProof.computable_ite ((tag_is 4).comp hc) hmul
            (ComputableMapAtomsProof.computable_ite ((tag_is 5).comp hc) hdiv
              (ComputableMapAtomsProof.computable_ite ((tag_is 6).comp hc) hphi
                (ComputableMapAtomsProof.computable_ite ((tag_is 8).comp hc) hinv (Computable.const 1))))))))
#print axioms graphAssemble_computable


end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
