module

public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivisionTargets
public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCodeEffectivity
public import LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearch

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision

theorem prepare_primitive_recursive : Primrec prepare := by
  have hn : Primrec (fun t : Input => t.1) := Primrec.fst
  have hb : Primrec (fun t : Input => t.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun t : Input => t.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq : Primrec (fun t : Input => t.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hpi := hn.pair (hb.pair (hb.pair hp))
  have hqi := hn.pair (hb.pair (hb.pair hq))
  have hpc := BoxPolynomialCode.rebase_primitive_recursive.comp hpi
  have hqc := BoxPolynomialCode.rebase_primitive_recursive.comp hqi
  exact (hpc.pair hqc).of_eq (fun _ => rfl)

theorem verify_primitive_recursive :
    Primrec (fun t : Input × PolynomialQuotientSearch.Certificate => verify t.1 t.2) := by
  have hn : Primrec (fun t : Input × PolynomialQuotientSearch.Certificate => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun t : Input × PolynomialQuotientSearch.Certificate => t.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hp : Primrec (fun t : Input × PolynomialQuotientSearch.Certificate => t.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hq : Primrec (fun t : Input × PolynomialQuotientSearch.Certificate => t.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hw : Primrec (fun t : Input × PolynomialQuotientSearch.Certificate => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun t : Input × PolynomialQuotientSearch.Certificate => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hbase := Primrec.nat_mul.comp (Primrec.const 2) hb
  have hpi := hn.pair (hb.pair (hbase.pair hp))
  have hwi := hn.pair (hb.pair (hbase.pair hw))
  have hqi := hn.pair (hb.pair (hbase.pair hq))
  have hpc := BoxPolynomialCode.rebase_primitive_recursive.comp hpi
  have hwc := BoxPolynomialCode.rebase_primitive_recursive.comp hwi
  have hqc := BoxPolynomialCode.rebase_primitive_recursive.comp hqi
  have hproduct := DensePolynomial.mul_primitive_recursive.comp hpc hwc
  have heq := PolynomialCertificateSearch.equal_primitive_recursive.comp hproduct hqc
  have hrem := DensePolynomial.isZero_primitive_recursive.comp hr
  exact (Primrec.and.comp hrem heq).of_eq (fun _ => rfl)

theorem search_partial_recursive : Targets.boundedDivisionSearchPartialRecursive := by
  have hs := PolynomialQuotientSearch.search_partial_recursive.comp
    prepare_primitive_recursive.to_comp
  exact hs.map verify_primitive_recursive.to_comp.to₂

end LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision
