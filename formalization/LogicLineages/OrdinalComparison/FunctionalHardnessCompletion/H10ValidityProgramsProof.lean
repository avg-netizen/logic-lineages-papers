module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ValidityTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.Proof
open LogicLineages.ComputabilityKnowledge.PolynomialCircuit
open LayeredComparison.IntegerAlgorithms.Proof (ofNat_primitive negate_primitive)

attribute [local irreducible] Nat.sqrt Nat.unpair

/-- List.all is implemented by ordinary primitive recursion over the list. -/
private theorem list_all_pr {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun x => (f x).all (g x)) := by
  apply (Primrec.list_foldr hf (Primrec.const true)
    (Primrec.and.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro x
  induction f x with
  | nil => rfl
  | cons b bs ih => simp [List.foldr, ih]

private theorem variables_pr : Primrec₂ variablesValid :=
  list_all_pr Primrec.snd
    (Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).decide.to₂

private theorem terms_pr : Primrec₂ termsValid :=
  list_all_pr Primrec.snd
    (variables_pr.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂

private theorem negSucc_pr : Primrec Int.negSucc :=
  (negate_primitive.comp (ofNat_primitive.comp Primrec.succ)).of_eq (fun _ => rfl)

private theorem pr_decodedCons : Primrec (fun p : Option Int × List Nat × Option Monomials =>
    p.1.bind (fun z => p.2.2.map ((z,p.2.1) :: ·))) := by
  apply Primrec.option_bind Primrec.fst
  apply Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (Primrec.list_cons.comp
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))) Primrec.snd).to₂

/-- The actual length-framed source parser is primitive recursive under the
standard Int encoding. The finite-recursion children and assembly stay local
to this proof; no alternate Code or Int instance is introduced. -/
private theorem pr_decodeTerms : Primrec decodeTerms := by
  let decodeCoeff (tag k : Nat) : Option Int :=
    if tag = 0 then some (.ofNat k) else if tag = 1 then some (.negSucc k) else none
  have pr_decodeCoeff : Primrec (fun p : Nat × Nat => decodeCoeff p.1 p.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
      (Primrec.option_some.comp (ofNat_primitive.comp Primrec.snd))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
        (Primrec.option_some.comp (negSucc_pr.comp Primrec.snd)) (Primrec.const none))
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

theorem validityPrimitive : Targets.ValidityPrimitive := by
  have hbody : Primrec (fun p : Nat × List Nat =>
      (decodeTerms p.2).any (termsValid p.1)) := by
    apply (Primrec.option_casesOn (pr_decodeTerms.comp Primrec.snd) (Primrec.const false)
      (terms_pr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
    intro p
    cases decodeTerms p.2 <;> rfl
  have h : Primrec (fun xs : List Nat => List.casesOn (motive := fun _ => Bool) xs false
      (fun n rest => (decodeTerms rest).any (termsValid n))) :=
    Primrec.list_casesOn Primrec.id (Primrec.const false) (hbody.comp Primrec.snd).to₂
  apply h.of_eq
  intro xs
  cases xs with
  | nil => rfl
  | cons n rest =>
    simp only [validInput, LogicLineages.ComputabilityKnowledge.PolynomialCircuit.decode,
      Option.any_map]

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.Proof
