module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryTuple
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
open GorbowSyntax GorbowStandardInstances GorbowRegistryTuple

theorem pairInjection : Comparators.GorbowRegistryTuple.PairInjection := by
  intro a b c d
  constructor
  · intro he
    have hs : a+b=c+d := by
      by_cases hs : a+b=c+d
      · exact hs
      · rcases lt_or_gt_of_ne hs with hl | hl
        · have hb := Nat.mul_self_le_mul_self (show a+b+1≤c+d by omega)
          unfold pair at he
          nlinarith
        · have hb := Nat.mul_self_le_mul_self (show c+d+1≤a+b by omega)
          unfold pair at he
          nlinarith
    unfold pair at he
    rw [hs] at he
    have ha : a=c := by omega
    exact ⟨ha,by omega⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem tupleInjection : Comparators.GorbowRegistryTuple.TupleInjection := by
  intro as bs h
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [tuple]
  | cons a as ih =>
    cases bs with
    | nil => simp [tuple] at h
    | cons b bs =>
      have hp : pair a (tuple as) = pair b (tuple bs) := by simpa [tuple] using h
      obtain ⟨rfl,ht⟩ := (pairInjection _ _ _ _).mp hp
      exact congrArg (List.cons a) (ih ht)

theorem headerInjection : Comparators.GorbowRegistryTuple.HeaderInjection := by
  intro arity tag args arity' tag' args'
  constructor
  · intro h
    obtain ⟨ha,ht⟩ := (pairInjection _ _ _ _).mp h
    obtain ⟨ht,hargs⟩ := (pairInjection _ _ _ _).mp ht
    exact ⟨ha,ht,tupleInjection hargs⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

private theorem pairBounds (a b : Nat) : a≤pair a b ∧ b≤pair a b := by
  have hs : a+b≤(a+b)*(a+b) := by
    cases h : a+b with
    | zero => simp [h]
    | succ k => nlinarith
  unfold pair
  constructor <;> omega

theorem bounds : Comparators.GorbowRegistryTuple.Bounds := by
  refine ⟨pairBounds,?_⟩
  intro a as
  have h := (pairBounds a (tuple as)).2
  change tuple as < pair a (tuple as)+1
  omega

private theorem pairArithmetic {n : Nat} {a b : Term n} (ha : ArithmeticTerm a) (hb : ArithmeticTerm b) :
    ArithmeticTerm (pairTerm a b) :=
  .add (.mul (.add ha hb) (.add ha hb)) ha
private theorem tupleArithmetic {n : Nat} (as : List (Term n)) (h : ∀ t ∈ as, ArithmeticTerm t) :
    ArithmeticTerm (tupleTerm as) := by
  induction as with
  | nil => exact .zero
  | cons a as ih =>
    exact .succ (pairArithmetic (h a (by simp)) (ih (fun t ht => h t (by simp [ht]))))

theorem arithmeticConstructors : Comparators.GorbowRegistryTuple.ArithmeticConstructors := by
  refine ⟨fun _ _ _ ha hb => pairArithmetic ha hb,fun _ as h => tupleArithmetic as h,?_⟩
  intro n arity tag as h
  exact pairArithmetic (GorbowStandardInstancesProof.arithmeticNumerals n arity)
    (pairArithmetic (GorbowStandardInstancesProof.arithmeticNumerals n tag) (tupleArithmetic as h))

private theorem pairValue {n : Nat} (I : Interpretation) (v : Fin n → Nat) (a b : Term n) :
    (pairTerm a b).realize I v = pair (a.realize I v) (b.realize I v) := rfl
private theorem tupleValue {n : Nat} (I : Interpretation) (v : Fin n → Nat) (as : List (Term n)) :
    (tupleTerm as).realize I v = tuple (as.map (fun t => t.realize I v)) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [tupleTerm,Term.realize,pairValue,ih,tuple]

theorem termCalibration : Comparators.GorbowRegistryTuple.TermCalibration := by
  intro n I v
  refine ⟨pairValue I v,tupleValue I v,?_⟩
  intro arity tag as
  simp [headerTerm,pairValue,numeral_realize,tupleValue,header]

private theorem pr_pair : Primrec (fun p : Nat × Nat => pair p.1 p.2) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)
    (Primrec.nat_add.comp Primrec.fst Primrec.snd)) Primrec.fst
private theorem pr_tuple : Primrec tuple := by
  have hs : Primrec (fun p : List Nat × Nat × Nat => pair p.2.1 p.2.2+1) :=
    Primrec.succ.comp (pr_pair.comp Primrec.snd)
  have h := Primrec.list_foldr (Primrec.id : Primrec (fun as : List Nat => as)) (Primrec.const 0) hs.to₂
  exact h.of_eq (fun as => by induction as with
    | nil => rfl
    | cons a as ih => simpa [tuple,List.foldr] using congrArg (fun n => pair a n+1) ih)
private theorem pr_header : Primrec (fun p : Nat × Nat × List Nat => header p.1 p.2.1 p.2.2) :=
  pr_pair.comp (Primrec.fst.pair (pr_pair.comp ((Primrec.fst.comp Primrec.snd).pair
    (pr_tuple.comp (Primrec.snd.comp Primrec.snd)))))

theorem uniformPrograms : Comparators.GorbowRegistryTuple.UniformPrograms := ⟨pr_pair,pr_tuple,pr_header⟩

theorem gorbowRegistryTuple : Comparators.GorbowRegistryTuple.Target :=
  ⟨pairInjection,tupleInjection,headerInjection,bounds,arithmeticConstructors,termCalibration,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
