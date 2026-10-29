module

public import LogicLineages.ComputabilityKnowledge.Comparators.PolynomialCircuitEffectivity

@[expose] public section

/-! External Codex continuation certificate for the concrete polynomial-code
compiler. All computation is on explicit finite data; no computability of the
abstract MvPolynomial representation is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.PolynomialCircuitEffectivityProof

open CircuitReduction PolynomialCircuit

private theorem terms_roundtrip (ms : Monomials) : decodeTerms (encodeTerms ms) = some ms := by
  induction ms with
  | nil => simp [encodeTerms,decodeTerms]
  | cons m ms ih =>
    rcases m with ⟨z,vs⟩
    cases z <;> simp [encodeTerms,decodeTerms,ih]

theorem inputCodecFaithful : Comparators.PolynomialCircuitEffectivity.InputCodecFaithful := by
  intro p
  simp [PolynomialCircuit.decode,PolynomialCircuit.encode,terms_roundtrip]

theorem codeCorrespondence : Comparators.PolynomialCircuitEffectivity.CodeCorrespondence := by
  intro p
  simp [PolynomialCircuit.compileCode,inputCodecFaithful p]

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

private def gateEquiv : Gate ≃ Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat)) where
  toFun | .constant k => .inl k | .add x y => .inr (.inl (x,y)) | .mul x y => .inr (.inr (x,y))
  invFun | .inl k => .constant k | .inr (.inl (x,y)) => .add x y | .inr (.inr (x,y)) => .mul x y
  left_inv := by intro g; cases g <;> rfl
  right_inv := by intro g; rcases g with k | (⟨x,y⟩ | ⟨x,y⟩) <;> rfl
private instance gatePrimcodable : Primcodable Gate := Primcodable.ofEquiv _ gateEquiv
private theorem pr_gateTo : Primrec gateEquiv := Primrec.of_equiv
private theorem pr_gateFrom : Primrec gateEquiv.symm := Primrec.of_equiv_symm
private theorem pr_constant : Primrec Gate.constant := pr_gateFrom.comp Primrec.sumInl
private theorem pr_add : Primrec (fun p : Nat × Nat => Gate.add p.1 p.2) :=
  pr_gateFrom.comp (Primrec.sumInr.comp Primrec.sumInl)
private theorem pr_mul : Primrec (fun p : Nat × Nat => Gate.mul p.1 p.2) :=
  pr_gateFrom.comp (Primrec.sumInr.comp Primrec.sumInr)

private def stateEquiv : State ≃ List Gate × Nat × Nat where
  toFun s := (s.gates,s.left,s.right)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv := by intro s; cases s; rfl
  right_inv := by intro s; rcases s with ⟨gs,l,r⟩; rfl
private instance statePrimcodable : Primcodable State := Primcodable.ofEquiv _ stateEquiv
private theorem pr_stateTo : Primrec stateEquiv := Primrec.of_equiv
private theorem pr_stateFrom : Primrec stateEquiv.symm := Primrec.of_equiv_symm
private theorem pr_gates : Primrec State.gates := Primrec.fst.comp pr_stateTo
private theorem pr_left : Primrec State.left := Primrec.fst.comp (Primrec.snd.comp pr_stateTo)
private theorem pr_right : Primrec State.right := Primrec.snd.comp (Primrec.snd.comp pr_stateTo)

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

private theorem pr_initial : Primrec initial :=
  pr_stateFrom.comp ((Primrec.const [Gate.constant 0,Gate.constant 0]).pair (Primrec.id.pair Primrec.succ))

private theorem pr_multiplyInputs : Primrec (fun p : Nat × List Nat => multiplyInputs p.1 p.2) := by
  let children : (Nat × List Nat) → List (Nat × List Nat) := fun p =>
    if p.2.length = 0 then [] else [(p.1+1,p.2.tail)]
  let assemble : (Nat × List Nat) → List (List Gate) → Option (List Gate) := fun p rs =>
    some (if p.2.length = 0 then [] else Gate.mul p.1 p.2.head! :: rs.head!)
  have hm := Primrec.list_length.comp (Primrec.snd : Primrec (fun p : Nat × List Nat => p.2))
  have hz := Primrec.eq.comp hm (Primrec.const 0)
  have hc : Primrec children := Primrec.ite hz (Primrec.const [])
    (Primrec.list_cons.comp ((Primrec.succ.comp Primrec.fst).pair (Primrec.list_tail.comp Primrec.snd)) (Primrec.const []))
  have ha : Primrec₂ assemble :=
    (Primrec.option_some.comp (Primrec.ite (hz.comp Primrec.fst) (Primrec.const [])
      (Primrec.list_cons.comp
        (pr_mul.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.list_headI.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.list_headI.comp Primrec.snd)))).to₂
  apply Primrec.nat_omega_rec' (fun p : Nat × List Nat => multiplyInputs p.1 p.2) hm hc ha
  · rintro ⟨acc,vs⟩ p hp
    cases vs with
    | nil => simp [children] at hp
    | cons i vs => simp [children] at hp; subst p; simp
  · rintro ⟨acc,vs⟩
    cases vs <;> simp [children,assemble,multiplyInputs]

private theorem pr_monomialGates : Primrec (fun p : Nat × Nat × List Nat => monomialGates p.1 p.2.1 p.2.2) :=
  Primrec.list_cons.comp (pr_constant.comp (Primrec.fst.comp Primrec.snd))
    (pr_multiplyInputs.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)))

private theorem pr_emit (pos : Bool) : Primrec (fun p : Nat × State × Nat × List Nat => emit p.1 pos p.2.1 p.2.2.1 p.2.2.2) := by
  let start (p : Nat × State × Nat × List Nat) := p.1 + p.2.1.gates.length
  let value (p : Nat × State × Nat × List Nat) := start p + p.2.2.2.length
  have hs : Primrec start := Primrec.nat_add.comp Primrec.fst
    (Primrec.list_length.comp (pr_gates.comp (Primrec.fst.comp Primrec.snd)))
  have hv : Primrec value := Primrec.nat_add.comp hs
    (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hl := pr_left.comp (Primrec.fst.comp (Primrec.snd : Primrec (fun p : Nat × State × Nat × List Nat => p.2)))
  have hr := pr_right.comp (Primrec.fst.comp (Primrec.snd : Primrec (fun p : Nat × State × Nat × List Nat => p.2)))
  have hprefix : Primrec (fun p : Nat × State × Nat × List Nat =>
      p.2.1.gates ++ monomialGates (start p) p.2.2.1 p.2.2.2) :=
    Primrec.list_append.comp (pr_gates.comp (Primrec.fst.comp Primrec.snd))
      (pr_monomialGates.comp (hs.pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hgs (old : (Nat × State × Nat × List Nat) → Nat) (ho : Primrec old) :
      Primrec (fun p => p.2.1.gates ++ monomialGates (start p) p.2.2.1 p.2.2.2 ++ [Gate.add (old p) (value p)]) :=
    Primrec.list_append.comp hprefix (Primrec.list_cons.comp (pr_add.comp (ho.pair hv)) (Primrec.const []))
  cases pos
  · exact pr_stateFrom.comp ((hgs _ hr).pair (hl.pair (Primrec.succ.comp hv)))
  · exact pr_stateFrom.comp ((hgs _ hl).pair ((Primrec.succ.comp hv).pair hr))

private theorem pr_emitApplied (pos : Bool) :
    Primrec₂ (fun p : Nat × State × Monomial => fun k => emit p.1 pos p.2.1 k p.2.2.2) := by
  have hm : Primrec (fun q : (Nat × State × Monomial) × Nat =>
      (q.1.1,q.1.2.1,q.2,q.1.2.2.2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  exact ((pr_emit pos).comp hm).to₂

private theorem pr_step : Primrec (fun p : Nat × State × Monomial => step p.1 p.2.1 p.2.2) := by
  have hi : Primrec (fun p : Nat × State × Monomial => intEquiv p.2.2.1) :=
    pr_intTo.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hp := Primrec.nat_casesOn' (Primrec.fst.comp Primrec.snd) (pr_emitApplied true)
  have h := Primrec.sumCasesOn hi hp (pr_emitApplied false)
  exact h.of_eq (fun p => by
    rcases p with ⟨n,s,z,vs⟩
    cases z with
    | ofNat k => cases k <;> rfl
    | negSucc k => rfl)

private theorem pr_build : Primrec build :=
  Primrec.list_foldl pr_terms (pr_initial.comp pr_input)
    (pr_step.comp ((pr_input.comp Primrec.fst).pair Primrec.snd)).to₂

private theorem pr_encodeGate : Primrec encodeGate := by
  have hp : Primrec (fun k : Nat => [0,k,0]) :=
    pr_cons (Primrec.const 0) (pr_cons Primrec.id (Primrec.const [0]))
  have ha : Primrec (fun p : Nat × Nat => [1,p.1,p.2]) :=
    pr_cons (Primrec.const 1) (pr_cons Primrec.fst (pr_cons Primrec.snd (Primrec.const [])))
  have hm : Primrec (fun p : Nat × Nat => [2,p.1,p.2]) :=
    pr_cons (Primrec.const 2) (pr_cons Primrec.fst (pr_cons Primrec.snd (Primrec.const [])))
  have h := Primrec.sumCasesOn pr_gateTo (hp.comp Primrec.snd).to₂
    (Primrec.sumCasesOn Primrec.snd (ha.comp Primrec.snd).to₂ (hm.comp Primrec.snd).to₂).to₂
  exact h.of_eq (fun g => by cases g <;> rfl)

private theorem pr_encodeGates : Primrec encodeGates := by
  have h : Primrec (fun gs : List Gate => gs.foldr (fun g rest => encodeGate g ++ rest) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (Primrec.list_append.comp (pr_encodeGate.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [encodeGates,ih]

private theorem pr_encodedCompile : Primrec (fun p => encodeCircuit (PolynomialCircuit.compile p)) :=
  pr_cons pr_input (pr_cons (pr_left.comp pr_build) (pr_cons (pr_right.comp pr_build)
    (pr_encodeGates.comp (pr_gates.comp pr_build))))

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

theorem compilerPrimrec : Primrec PolynomialCircuit.compileCode :=
  Primrec.option_map pr_decode (pr_encodedCompile.comp Primrec.snd).to₂

theorem polynomialCircuitEffectivity : Comparators.PolynomialCircuitEffectivity.Target :=
  ⟨inputCodecFaithful,codeCorrespondence,compilerPrimrec.to_comp⟩

end LogicLineages.ComputabilityKnowledge.PolynomialCircuitEffectivityProof
