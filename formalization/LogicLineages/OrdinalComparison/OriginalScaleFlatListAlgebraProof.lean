module
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListTargets
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList.Proof
open SignedPair SignedPair.Proof FunctionalDetector.Proof HeterogeneousUnaryAssembly

private theorem signedCNF_injective : Function.Injective signedCNF := by
  intro a b he
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  have hei := congrArg (fun f : CantorGroup => f e) he
  simp only [cnf_apply] at hei
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite b e)
  rw [hm,hn,finite_nat,finite_nat] at hei
  have hmn : m=n := by exact_mod_cast hei
  rw [hm,hn,hmn]

private theorem cnf_add_nat (a : Ordinal) (n : Nat) :
    signedCNF (a+(n:Ordinal)) = signedCNF a + Finsupp.single 0 (n:Int) := by
  rw [← actualNaturalSumFiniteRight a n,cnf_sum,cnf_nat]

private noncomputable def coefficientTotal (hs : List Ordinal) (e : Ordinal) : Int :=
  (hs.map (fun a => signedCNF a e)).sum

private theorem coefficientTotal_append (xs ys : List Ordinal) (e : Ordinal) :
    coefficientTotal (xs++ys) e = coefficientTotal xs e + coefficientTotal ys e := by
  simp [coefficientTotal,List.map_append,List.sum_append]

private theorem cnf_fold (hs : List Ordinal) (e : Ordinal) :
    signedCNF (hs.foldr ordinalNaturalSum 0) e = coefficientTotal hs e := by
  induction hs with
  | nil => simp [coefficientTotal,show signedCNF 0=0 by simpa using cnf_nat 0]
  | cons a hs ih => simp only [List.foldr_cons,cnf_sum,Finsupp.add_apply,ih,
      coefficientTotal,List.map_cons,List.sum_cons]

private theorem cnf_charged (hs : List Ordinal) (e : Ordinal) :
    signedCNF (chargedSum hs) e = coefficientTotal hs e +
      if e=0 then (3*(hs.length:Int)+1) else 0 := by
  induction hs with
  | nil =>
    have hone : signedCNF (1:Ordinal)=Finsupp.single 0 (1:Int) := by simpa using cnf_nat 1
    simp [chargedSum,coefficientTotal,hone,Finsupp.single_apply,eq_comm]
  | cons a hs ih =>
    have hthree : signedCNF (a+3)=signedCNF a+Finsupp.single 0 (3:Int) := by
      simpa using cnf_add_nat a 3
    rw [chargedSum,cnf_sum,hthree]
    simp only [Finsupp.add_apply,ih,coefficientTotal,List.map_cons,List.sum_cons,
      List.length_cons,Nat.cast_add,Nat.cast_one]
    by_cases he : e=0
    · simp [he]
      omega
    · simp [Finsupp.single_apply,he,Ne.symm he]

private theorem coefficientTotal_copies (hs : List Ordinal) (n : Nat) (e : Ordinal) :
    coefficientTotal (List.replicate n hs).flatten e = (n:Int)*coefficientTotal hs e := by
  induction n with
  | zero => simp [coefficientTotal]
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons,coefficientTotal_append,ih]
    simp only [Nat.cast_add,Nat.cast_one]
    ring

private theorem coefficientTotal_replicate (a : Ordinal) (n : Nat) (e : Ordinal) :
    coefficientTotal (List.replicate n a) e = (n:Int)*signedCNF a e := by
  induction n with
  | zero => simp [coefficientTotal]
  | succ n ih =>
    simp only [List.replicate_succ,coefficientTotal,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    simp only [Nat.cast_add,Nat.cast_one]
    ring

private theorem copies_length (hs : List Ordinal) (n : Nat) :
    (List.replicate n hs).flatten.length = n*hs.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,ih,Nat.succ_mul,Nat.add_comm]

private theorem nat_below (n : Nat) : (n:Ordinal)<epsilonZero := by
  have h := normalRepresentationSound (NONote.ofNat n)
  change (ONote.ofNat n).repr < epsilonZero at h
  simpa only [ONote.repr_ofNat] using h

private theorem fold_below (hs : List Ordinal) (hh : ∀ a∈hs,a<epsilonZero) :
    hs.foldr ordinalNaturalSum 0 < epsilonZero := by
  induction hs with
  | nil => simpa using nat_below 0
  | cons a hs ih =>
    exact sum_below_epsilon a _ (hh a (by simp)) (ih (fun b hb => hh b (by simp [hb])))

theorem flat_balance (hs : List Ordinal) (a : Ordinal) (n c : Nat)
    (hhs : ∀ x∈hs,x<epsilonZero) (ha : a<epsilonZero) (hn : 2≤n)
    (hc : 3*hs.length+4≤c) :
    ordinalNaturalProduct (n:Ordinal) (ordinalNaturalSum (hs.foldr ordinalNaturalSum 0+(c:Ordinal)) a) =
      chargedSum ((List.replicate n hs).flatten ++ List.replicate n a) +
        ((n*(c-3*hs.length-3)-1:Nat):Ordinal) := by
  have hb : ordinalNaturalSum (hs.foldr ordinalNaturalSum 0+(c:Ordinal)) a < epsilonZero := by
    apply sum_below_epsilon _ _ _ ha
    rw [← actualNaturalSumFiniteRight]
    exact sum_below_epsilon _ _ (fold_below hs hhs) (nat_below c)
  let d : Nat := c-3*hs.length-3
  let g : Nat := n*d-1
  have hd : 1≤d := by dsimp [d]; omega
  have hceq : c=3*hs.length+3+d := by dsimp [d]; omega
  have hnd : 1≤n*d := by nlinarith
  have hgeq : g+1=n*d := by dsimp [g]; omega
  have hcI : (c:Int)=3*(hs.length:Int)+3+(d:Int) := by exact_mod_cast hceq
  have hgI : (g:Int)+1=(n:Int)*(d:Int) := by exact_mod_cast hgeq
  apply signedCNF_injective
  have hp := cnf_finite_product (⟨n,by omega⟩ : ℕ+)
    (ordinalNaturalSum (hs.foldr ordinalNaturalSum 0+(c:Ordinal)) a) hb
  change signedCNF (ordinalNaturalProduct (n:Ordinal)
      (ordinalNaturalSum (hs.foldr ordinalNaturalSum 0+(c:Ordinal)) a)) =
    (n:Int) • signedCNF (ordinalNaturalSum (hs.foldr ordinalNaturalSum 0+(c:Ordinal)) a) at hp
  rw [hp,cnf_sum,cnf_add_nat,cnf_add_nat]
  ext e
  simp only [Finsupp.smul_apply,Finsupp.add_apply,smul_eq_mul,cnf_fold,cnf_charged,
    coefficientTotal_append,coefficientTotal_copies,coefficientTotal_replicate,
    List.length_append,copies_length,List.length_replicate,Nat.cast_add,Nat.cast_mul]
  change (n:Int)*(coefficientTotal hs e + (Finsupp.single 0 (c:Int)) e + signedCNF a e) =
    (n:Int)*coefficientTotal hs e + (n:Int)*signedCNF a e +
      (if e=0 then 3*((n:Int)*(hs.length:Int)+(n:Int))+1 else 0) + (Finsupp.single 0 (g:Int)) e
  by_cases he : e=0
  · simp only [he,Finsupp.single_eq_same,ite_true]
    rw [hcI]
    nlinarith [hgI]
  · simp only [Finsupp.single_apply,he,Ne.symm he,ite_false,add_zero]
    ring

end LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList.Proof
