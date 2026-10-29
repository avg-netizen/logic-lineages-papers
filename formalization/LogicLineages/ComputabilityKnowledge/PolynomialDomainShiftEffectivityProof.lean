module

public import LogicLineages.ComputabilityKnowledge.Comparators.PolynomialDomainShiftEffectivity
public import LogicLineages.ComputabilityKnowledge.PolynomialCircuitEffectivityProof

@[expose] public section

/-! External Codex continuation: primitive-recursive literal finite expansion
on the existing coefficient/variable-list codec. The concrete codec helper
proofs reproduce the checked public front-end construction, not private imports. -/
namespace LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftEffectivityProof

open PolynomialCircuit PolynomialDomainShift

theorem inputCodecFaithful : Comparators.PolynomialDomainShiftEffectivity.InputCodecFaithful :=
  PolynomialCircuitEffectivityProof.inputCodecFaithful

theorem outputCodecFaithful : Comparators.PolynomialDomainShiftEffectivity.OutputCodecFaithful := by
  intro p q h
  have he := congrArg PolynomialCircuit.decode h
  rw [inputCodecFaithful p,inputCodecFaithful q] at he
  exact Option.some.inj he

theorem codeCorrespondence : Comparators.PolynomialDomainShiftEffectivity.CodeCorrespondence := by
  intro p
  unfold encodedShift
  rw [inputCodecFaithful p]
  rfl

private def intEquiv : Int ≃ Nat ⊕ Nat where
  toFun | .ofNat n => .inl n | .negSucc n => .inr n
  invFun | .inl n => .ofNat n | .inr n => .negSucc n
  left_inv := by intro z; cases z <;> rfl
  right_inv := by intro z; cases z <;> rfl
private instance intPrimcodable : Primcodable Int := Primcodable.ofEquiv _ intEquiv
private theorem pr_intTo : Primrec intEquiv := Primrec.of_equiv
private theorem pr_intFrom : Primrec intEquiv.symm := Primrec.of_equiv_symm
private theorem pr_ofNat : Primrec Int.ofNat := pr_intFrom.comp Primrec.sumInl
private theorem pr_negSucc : Primrec Int.negSucc := pr_intFrom.comp Primrec.sumInr


private def codeEquiv : Code ≃ Nat × Monomials where
  toFun p := (p.inputCount,p.monomials)
  invFun p := ⟨p.1,p.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl
private instance codePrimcodable : Primcodable Code := Primcodable.ofEquiv _ codeEquiv
private theorem pr_codeTo : Primrec codeEquiv := Primrec.of_equiv
private theorem pr_codeFrom : Primrec codeEquiv.symm := Primrec.of_equiv_symm
private theorem pr_input : Primrec Code.inputCount := Primrec.fst.comp pr_codeTo
private theorem pr_terms : Primrec Code.monomials := Primrec.snd.comp pr_codeTo

private theorem pr_cons {α : Type} [Primcodable α] {a : α → Nat} {b : α → List Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => a x :: b x) := Primrec.list_cons.comp ha hb


private def decodeCoeff (tag k : Nat) : Option Int :=
  if tag = 0 then some (.ofNat k) else if tag = 1 then some (.negSucc k) else none

private theorem pr_decodeCoeff : Primrec (fun p : Nat × Nat => decodeCoeff p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.option_some.comp (pr_ofNat.comp Primrec.snd))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (Primrec.option_some.comp (pr_negSucc.comp Primrec.snd)) (Primrec.const none))

private theorem pr_decodedCons : Primrec (fun p : Option Int × List Nat × Option Monomials =>
    p.1.bind (fun z => p.2.2.map ((z,p.2.1) :: ·))) := by
  apply Primrec.option_bind Primrec.fst
  apply Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (Primrec.list_cons.comp
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))) Primrec.snd).to₂

private theorem pr_decodeTerms : Primrec decodeTerms := by
  let children : List Nat → List (List Nat) := fun xs =>
    if 3 ≤ xs.length then [(xs.drop 3).drop (xs.getD 2 0)] else []
  let assemble : List Nat → List (Option Monomials) → Option (Option Monomials) := fun xs rs =>
    some (if 3 ≤ xs.length then
      if xs.getD 2 0 ≤ (xs.drop 3).length then
        (decodeCoeff (xs.getD 0 0) (xs.getD 1 0)).bind
          (fun z => rs.head!.map ((z,(xs.drop 3).take (xs.getD 2 0)) :: ·))
      else none
    else if xs.length = 0 then some [] else none)
  have hg (i : Nat) : Primrec (fun xs : List Nat => xs.getD i 0) :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.const i)
  have hd : Primrec (fun xs : List Nat => xs.drop 3) := Primrec.list_drop.comp (Primrec.const 3) Primrec.id
  have hc : PrimrecPred (fun xs : List Nat => 3 ≤ xs.length) := Primrec.nat_le.comp (Primrec.const 3) Primrec.list_length
  have hchildren : Primrec children := Primrec.ite hc
    (Primrec.list_cons.comp (Primrec.list_drop.comp (hg 2) hd) (Primrec.const [])) (Primrec.const [])
  have ha : Primrec₂ assemble := by
    apply Primrec.option_some.comp
    apply Primrec.ite (hc.comp Primrec.fst)
    · apply Primrec.ite ((Primrec.nat_le.comp (hg 2) (Primrec.list_length.comp hd)).comp Primrec.fst)
      · refine pr_decodedCons.comp (g := fun p : List Nat × List (Option Monomials) =>
          (decodeCoeff (p.1.getD 0 0) (p.1.getD 1 0), (p.1.drop 3).take (p.1.getD 2 0), p.2.head!)) ?_
        exact (pr_decodeCoeff.comp (((hg 0).comp Primrec.fst).pair ((hg 1).comp Primrec.fst))).pair
          ((Primrec.list_take.comp ((hg 2).comp Primrec.fst) (hd.comp Primrec.fst)).pair
            (Primrec.list_headI.comp Primrec.snd))
      · exact Primrec.const none
    · exact Primrec.ite ((Primrec.eq.comp Primrec.list_length (Primrec.const 0)).comp Primrec.fst)
        (Primrec.const (some [])) (Primrec.const none)
  apply Primrec.nat_omega_rec' decodeTerms Primrec.list_length hchildren ha
  · intro xs ys hy
    by_cases h : 3 ≤ xs.length
    · simp [children,h] at hy
      subst ys
      simp only [List.length_drop]
      omega
    · simp [children,h] at hy
  · intro xs
    cases xs with
    | nil => simp [children,assemble,decodeTerms]
    | cons tag xs =>
      cases xs with
      | nil => simp [children,assemble,decodeTerms]
      | cons k xs =>
        cases xs with
        | nil => simp [children,assemble,decodeTerms]
        | cons len rest =>
          have hd3 (j : Nat) : (tag::k::len::rest).drop (3+j) = rest.drop j := by
            rw [Nat.add_comm]
            rfl
          cases tag with
          | zero => simp [children,assemble,decodeTerms,decodeCoeff,hd3]
          | succ tag => cases tag <;> simp [children,assemble,decodeTerms,decodeCoeff,hd3]

private theorem pr_decode : Primrec PolynomialCircuit.decode := by
  have hcons : Primrec₂ (fun _ : List Nat => fun p : Nat × List Nat =>
      (decodeTerms p.2).map (fun ms => codeEquiv.symm (p.1,ms))) := by
    apply Primrec.option_map (pr_decodeTerms.comp (Primrec.snd.comp Primrec.snd))
    exact (pr_codeFrom.comp ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to₂
  have h := Primrec.list_casesOn Primrec.id (Primrec.const none) hcons
  exact h.of_eq (fun xs => by cases xs <;> rfl)


private theorem pr_neg : Primrec (fun z : Int => -z) := by
  have hp : Primrec (fun n : Nat => Nat.casesOn (motive := fun _ => Int) n (Int.ofNat 0) Int.negSucc) :=
    Primrec.nat_casesOn₁ (Int.ofNat 0) pr_negSucc
  have hn := pr_ofNat.comp Primrec.succ
  have h := Primrec.sumCasesOn pr_intTo (hp.comp Primrec.snd).to₂ (hn.comp Primrec.snd).to₂
  exact h.of_eq (fun z => by cases z with | ofNat n => cases n <;> rfl | negSucc n => rfl)

private theorem pr_attach : Primrec (fun p : Nat × Monomial => attachVariable p.1 p.2) :=
  (Primrec.fst.comp Primrec.snd).pair
    (Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

private theorem pr_negateCoefficient : Primrec negateCoefficient :=
  (pr_neg.comp Primrec.fst).pair Primrec.snd

private theorem pr_expandStep : Primrec (fun p : Nat × Monomials =>
    p.2.map (attachVariable p.1) ++ p.2.map negateCoefficient) := by
  apply Primrec.list_append.comp
  · exact Primrec.list_map Primrec.snd
      (pr_attach.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  · exact Primrec.list_map Primrec.snd (pr_negateCoefficient.comp Primrec.snd).to₂

private theorem pr_expand : Primrec expand :=
  Primrec.list_foldr Primrec.snd
    (Primrec.list_cons.comp (Primrec.fst.pair (Primrec.const [])) (Primrec.const []))
    (pr_expandStep.comp Primrec.snd).to₂

private theorem pr_shiftTerms : Primrec shiftTerms :=
  Primrec.list_flatMap Primrec.id (pr_expand.comp Primrec.snd).to₂

private theorem pr_shift : Primrec shift :=
  pr_codeFrom.comp (pr_input.pair (pr_shiftTerms.comp pr_terms))

private def encodeOne (m : Monomial) : List Nat :=
  match m.1 with
  | .ofNat k => 0 :: k :: m.2.length :: m.2
  | .negSucc k => 1 :: k :: m.2.length :: m.2

private theorem pr_encodeOne : Primrec encodeOne := by
  have body (tag : Nat) : Primrec₂ (fun m : Monomial => fun k : Nat => tag :: k :: m.2.length :: m.2) :=
    (pr_cons (Primrec.const tag) (pr_cons Primrec.snd
      (pr_cons (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)))).to₂
  have h := Primrec.sumCasesOn (pr_intTo.comp Primrec.fst) (body 0) (body 1)
  exact h.of_eq (fun m => by rcases m with ⟨z,vs⟩; cases z <;> rfl)

private theorem encodeTerms_flatMap (ms : Monomials) : ms.flatMap encodeOne = encodeTerms ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    cases z <;> simp [encodeOne,encodeTerms,ih]

private theorem pr_encodeTerms : Primrec encodeTerms :=
  (Primrec.list_flatMap Primrec.id (pr_encodeOne.comp Primrec.snd).to₂).of_eq encodeTerms_flatMap

private theorem pr_encode : Primrec PolynomialCircuit.encode :=
  pr_cons pr_input (pr_encodeTerms.comp pr_terms)

theorem shiftPrimrec : Primrec encodedShift :=
  Primrec.option_map pr_decode ((pr_encode.comp pr_shift).comp Primrec.snd).to₂

theorem polynomialDomainShiftEffectivity : Comparators.PolynomialDomainShiftEffectivity.Target :=
  ⟨inputCodecFaithful,outputCodecFaithful,codeCorrespondence,shiftPrimrec.to_comp⟩

end LogicLineages.ComputabilityKnowledge.PolynomialDomainShiftEffectivityProof
