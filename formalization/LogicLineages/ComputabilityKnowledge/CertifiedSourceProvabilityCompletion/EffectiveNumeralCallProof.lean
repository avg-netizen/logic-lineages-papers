module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralEqualityProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
open GorbowSyntax GorbowRegistryTuple GorbowPRDefiningEquations

variable {alpha : Type} [Primcodable alpha]

private theorem rawArgumentsEffective {n arity : Nat}
    (args : alpha → List.Vector (Term n) arity)
    (ha : ∀ i, TermEffective (fun x => (args x).get i)) :
    Primrec (fun x => (args x).toList.map GorbowTermPrefixCode.encode) := by
  have h := Primrec.list_ofFn ha
  apply h.of_eq
  intro x
  calc
    List.ofFn (fun i => GorbowTermPrefixCode.encode ((args x).get i)) =
        (List.Vector.ofFn (args x).get).toList.map GorbowTermPrefixCode.encode := by
      simp only [List.Vector.toList_ofFn, List.map_ofFn, Function.comp_def]
    _ = _ := by rw [List.Vector.ofFn_get]

namespace TermEffective

theorem pair {n : Nat} {t u : alpha → Term n} (ht : TermEffective t) (hu : TermEffective u) :
    TermEffective (fun x => pairTerm (t x) (u x)) :=
  ((ht.add hu).mul (ht.add hu)).add ht

theorem tuple {n arity : Nat} (args : alpha → List.Vector (Term n) arity)
    (ha : ∀ i, TermEffective (fun x => (args x).get i)) :
    TermEffective (fun x => tupleTerm (args x).toList) := by
  have h := GorbowRegistryTermCodeProof.uniformPrograms.2.1.comp (rawArgumentsEffective args ha)
  exact h.of_eq (fun x => GorbowRegistryTermCodeProof.tupleCalibration n (args x).toList)

theorem header {n arity : Nat} {tag : alpha → Nat} (htag : Primrec tag)
    (args : alpha → List.Vector (Term n) arity)
    (ha : ∀ i, TermEffective (fun x => (args x).get i)) :
    TermEffective (fun x => headerTerm arity (tag x) (args x).toList) := by
  have h := GorbowRegistryTermCodeProof.uniformPrograms.2.2.1.comp
    ((Primrec.const arity).pair (htag.pair (rawArgumentsEffective args ha)))
  exact h.of_eq (fun x => GorbowRegistryTermCodeProof.headerCalibration n arity (tag x) (args x).toList)

theorem call {n arity : Nat} {tag : alpha → Nat} (htag : Primrec tag)
    (args : alpha → List.Vector (Term n) arity)
    (ha : ∀ i, TermEffective (fun x => (args x).get i)) :
    TermEffective (fun x => GorbowPRDefiningEquations.call (tag x) (args x)) :=
  (header htag args ha).universalFunction

end TermEffective

namespace HasCertificates

theorem pairCongruence (axCheck : alpha → List Nat → Bool)
    {a b c d : alpha → Term 0}
    (ha : TermEffective a) (hb : TermEffective b) (hc : TermEffective c) (hd : TermEffective d)
    (hac : HasCertificates axCheck (fun x => Formula.equal (a x) (c x)))
    (hbd : HasCertificates axCheck (fun x => Formula.equal (b x) (d x))) :
    HasCertificates axCheck (fun x => Formula.equal (pairTerm (a x) (b x)) (pairTerm (c x) (d x))) := by
  have hs := addCongruence axCheck ha hb hc hd hac hbd
  have hm := mulCongruence axCheck (ha.add hb) (ha.add hb) (hc.add hd) (hc.add hd) hs hs
  exact addCongruence axCheck ((ha.add hb).mul (ha.add hb)) ha
    ((hc.add hd).mul (hc.add hd)) hc hm hac

private theorem tupleZero (v : List.Vector (Term 0) 0) : tupleTerm v.toList = .zero := by
  have hv : v = List.Vector.nil := by
    apply List.Vector.ext
    intro i
    exact Fin.elim0 i
  rw [hv]
  rfl

private theorem tupleSucc {n : Nat} (v : List.Vector (Term 0) (n+1)) :
    tupleTerm v.toList = .succ (pairTerm v.head (tupleTerm v.tail.toList)) := by
  rw [← List.Vector.cons_head_tail v]
  rfl

theorem tupleCongruence (axCheck : alpha → List Nat → Bool) :
    ∀ arity (args others : alpha → List.Vector (Term 0) arity),
    (∀ i, TermEffective (fun x => (args x).get i)) →
    (∀ i, TermEffective (fun x => (others x).get i)) →
    (∀ i, HasCertificates axCheck (fun x => Formula.equal ((args x).get i) ((others x).get i))) →
    HasCertificates axCheck (fun x => Formula.equal (tupleTerm (args x).toList) (tupleTerm (others x).toList)) := by
  intro arity
  induction arity with
  | zero =>
      intro args others _ _ _
      have h := reflexive axCheck (TermEffective.constant (Term.zero : Term 0))
      simpa only [tupleZero] using h
  | succ n ih =>
      intro args others ha hb hc
      have hat : ∀ i, TermEffective (fun x => ((args x).tail).get i) := by
        intro i
        have he : (fun x : alpha => ((args x).tail).get i) =
            (fun x => (args x).get i.succ) := by
          funext x
          exact List.Vector.get_tail_succ (args x) i
        rw [he]
        exact ha i.succ
      have hbt : ∀ i, TermEffective (fun x => ((others x).tail).get i) := by
        intro i
        have he : (fun x : alpha => ((others x).tail).get i) =
            (fun x => (others x).get i.succ) := by
          funext x
          exact List.Vector.get_tail_succ (others x) i
        rw [he]
        exact hb i.succ
      have hct : ∀ i, HasCertificates axCheck (fun x => Formula.equal
          (((args x).tail).get i) (((others x).tail).get i)) := by
        intro i
        have he : (fun x : alpha => Formula.equal (((args x).tail).get i)
            (((others x).tail).get i)) = (fun x => Formula.equal ((args x).get i.succ)
              ((others x).get i.succ)) := by
          funext x
          exact congrArg₂ (fun a b : Term 0 => Formula.equal a b)
            (List.Vector.get_tail_succ (args x) i)
            (List.Vector.get_tail_succ (others x) i)
        rw [he]
        exact hc i.succ
      have ht := ih (fun x => (args x).tail) (fun x => (others x).tail) hat hbt hct
      have hah : TermEffective (fun x => (args x).head) := by
        simpa only [List.Vector.get_zero] using ha 0
      have hbh : TermEffective (fun x => (others x).head) := by
        simpa only [List.Vector.get_zero] using hb 0
      have hch : HasCertificates axCheck (fun x => Formula.equal (args x).head (others x).head) := by
        simpa only [List.Vector.get_zero] using hc 0
      have hp := pairCongruence axCheck hah (TermEffective.tuple _ hat)
        hbh (TermEffective.tuple _ hbt) hch ht
      have hs := successorCongruence axCheck (hah.pair (TermEffective.tuple _ hat))
        (hbh.pair (TermEffective.tuple _ hbt)) hp
      simpa only [tupleSucc] using hs

/-- The runtime tag occurs only in reflexive header components. No induction
on a runtime numeral AST or a different registry is required. -/
theorem callCongruence (axCheck : alpha → List Nat → Bool) {arity : Nat}
    {tag : alpha → Nat} (htag : Primrec tag)
    (args others : alpha → List.Vector (Term 0) arity)
    (ha : ∀ i, TermEffective (fun x => (args x).get i))
    (hb : ∀ i, TermEffective (fun x => (others x).get i))
    (hc : ∀ i, HasCertificates axCheck (fun x => Formula.equal ((args x).get i) ((others x).get i))) :
    HasCertificates axCheck (fun x => Formula.equal (call (tag x) (args x)) (call (tag x) (others x))) := by
  have htagT : TermEffective (fun x => (Term.numeral (tag x) : Term 0)) := TermEffective.numeral htag
  have harity : TermEffective (fun _ : alpha => (Term.numeral arity : Term 0)) :=
    TermEffective.constant _
  have ht := tupleCongruence axCheck arity args others ha hb hc
  have hp := pairCongruence axCheck htagT (TermEffective.tuple args ha)
    htagT (TermEffective.tuple others hb) (reflexive axCheck htagT) ht
  have hh := pairCongruence axCheck harity (htagT.pair (TermEffective.tuple args ha))
    harity (htagT.pair (TermEffective.tuple others hb)) (reflexive axCheck harity) hp
  exact universalFunctionCongruence axCheck (TermEffective.header htag args ha)
    (TermEffective.header htag others hb) hh

end HasCertificates
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
