module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchTargets
public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialEffectivity

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch

theorem degree_primitive_recursive : Primrec degree := by
  exact Primrec.nat_findGreatest
    (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
    ((Primrec.eq.comp
      (RationalCode.isZero_primitive_recursive.comp
        ((Primrec.list_getD RationalCode.zero).comp Primrec.fst Primrec.snd))
      (Primrec.const false)).primrecRel)

theorem equal_primitive_recursive : Primrec₂ equal :=
  DensePolynomial.isZero_primitive_recursive.comp
    (DensePolynomial.add_primitive_recursive.comp Primrec.fst
      (DensePolynomial.neg_primitive_recursive.comp Primrec.snd))

theorem verify_primitive_recursive : Primrec (fun t : Input × Certificate => verify t.1.1 t.1.2 t.2) := by
  let hb : Primrec (fun t : Input × Certificate => t.1.1) := Primrec.fst.comp Primrec.fst
  let ha : Primrec (fun t : Input × Certificate => t.1.2) := Primrec.snd.comp Primrec.fst
  let hq : Primrec (fun t : Input × Certificate => t.2.1) := Primrec.fst.comp Primrec.snd
  let hr : Primrec (fun t : Input × Certificate => t.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp
    (equal_primitive_recursive.comp ha
      (DensePolynomial.add_primitive_recursive.comp
        (DensePolynomial.mul_primitive_recursive.comp hb hq) hr))
    (Primrec.or.comp (DensePolynomial.isZero_primitive_recursive.comp hr)
      ((Primrec.nat_lt.comp (degree_primitive_recursive.comp hr)
        (degree_primitive_recursive.comp hb)).decide))

theorem atIndex_primitive_recursive : Primrec₂ atIndex := by
  apply Primrec.ite
    (Primrec.eq.comp (DensePolynomial.isZero_primitive_recursive.comp
      (Primrec.fst.comp Primrec.fst)) (Primrec.const true))
    (Primrec.option_some.comp (DensePolynomial.isZero_primitive_recursive.comp
      (Primrec.snd.comp Primrec.fst)))
  apply Primrec.option_bind (Primrec.decode.comp Primrec.snd)
  apply Primrec.ite
    (Primrec.eq.comp
      (verify_primitive_recursive.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
      (Primrec.const true))
    (Primrec.option_some.comp (DensePolynomial.isZero_primitive_recursive.comp
      (Primrec.snd.comp Primrec.snd)))
    (Primrec.const none)

theorem finite_primitive_recursive : Targets.polynomialSearchFinitePrimitiveRecursive :=
  ⟨degree_primitive_recursive, equal_primitive_recursive, verify_primitive_recursive,
    atIndex_primitive_recursive⟩

theorem search_partial_recursive : Targets.polynomialSearchPartialRecursive :=
  Partrec.rfindOpt atIndex_primitive_recursive.to_comp

end LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch
