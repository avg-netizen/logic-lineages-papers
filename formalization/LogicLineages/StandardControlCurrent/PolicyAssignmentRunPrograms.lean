module
public import LogicLineages.StandardControlCurrent.PolicyAssignmentBasePrograms
public import LogicLineages.StandardControlCurrent.ComputableRankedProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAssignmentRunPrograms
open OrdinalComparison Source Source.AdmissibleSum Source.SyntaxCode Source.OrdinalSyntax

theorem assignment (pol : Policy) (hpol : PolicyShape.Effective pol) :
    Computable (fun x : List Nat × Nat => PolicyAssignment.assignmentCode pol x.1 x.2) := by
  let S := List Nat×Nat
  let children : S → List S := fun s =>
    if s.2%8=5 then [(s.1,(s.2/8).unpair.1),(s.1,(s.2/8).unpair.2)]
    else if s.2%8=6 then [((s.2/8).unpair.1::s.1,(s.2/8).unpair.2)] else []
  let finish : S×List (Option (List Nat)) → Nat → Option (List Nat) := fun p resultType =>
    if p.1.2%8<5 then PolicyAssignment.primeCode pol (p.1.2%8) (p.1.2/8) (typeLevel resultType)
    else if p.1.2%8=5 then (check p.1.1 (p.1.2/8).unpair.2).bind (fun argType =>
      (p.2.getD 0 none).bind (fun f => (p.2.getD 1 none).bind (fun a =>
        PolicyConstructors.applicationCode pol (typeLevel resultType) (typeLevel argType) f a)))
    else if p.1.2%8=6 then (check ((p.1.2/8).unpair.1::p.1.1) (p.1.2/8).unpair.2).bind (fun bodyType =>
      (p.2.getD 0 none).bind (fun b => PolicyAbstraction.abstractionCode pol (typeLevel (p.1.2/8).unpair.1) (typeLevel bodyType) b))
    else none
  let assemble : S → List (Option (List Nat)) → Option (Option (List Nat)) := fun s rs =>
    some ((check s.1 s.2).bind (finish (s,rs)))
  have htag : Primrec (fun s : S => s.2%8) := Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
  have hpay : Primrec (fun s : S => s.2/8) := Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : S => s.2%8=k) := Primrec.eq.comp htag (Primrec.const k)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 6)
      (Primrec.list_cons.comp ((Primrec.list_cons.comp hl Primrec.fst).pair hr) (Primrec.const []))
      (Primrec.const []))
  have hf : Computable (fun x : (S×List (Option (List Nat)))×Nat => finish x.1 x.2) := by
    let P := (S×List (Option (List Nat)))×Nat
    have hs : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
    have ht' := htag.comp hs
    have hp' := hpay.comp hs
    have hl' := hl.comp hs
    have hr' := hr.comp hs
    have hg (k : Nat) : Primrec (fun p : P => p.1.2.getD k none) :=
      (Primrec.list_getD (none : Option (List Nat))).comp (Primrec.snd.comp Primrec.fst) (Primrec.const k)
    have level : Primrec typeLevel := SyntaxCode.StatementChecks.typeLevelPrimitiveRecursive
    have happ : Computable (fun p : P => (check p.1.1.1 (p.1.1.2/8).unpair.2).bind (fun a =>
      (p.1.2.getD 0 none).bind (fun f => (p.1.2.getD 1 none).bind (fun b =>
        PolicyConstructors.applicationCode pol (typeLevel p.2) (typeLevel a) f b)))) := by
      apply Computable.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.to_comp.comp
        (((Primrec.fst.comp hs).pair hr').to_comp))
      exact Computable.comp
        (f := fun q : Nat×Nat×Option (List Nat)×Option (List Nat) =>
          q.2.2.1.bind (fun f => q.2.2.2.bind (fun a => PolicyConstructors.applicationCode pol q.1 q.2.1 f a)))
        (g := fun q : P×Nat => (typeLevel q.1.2,typeLevel q.2,q.1.1.2.getD 0 none,q.1.1.2.getD 1 none))
        (PolicyAssignmentBasePrograms.appBind pol hpol)
        (((level.comp (Primrec.snd.comp Primrec.fst)).pair
          ((level.comp Primrec.snd).pair (((hg 0).comp Primrec.fst).pair ((hg 1).comp Primrec.fst)))).to_comp)
    have hlam : Computable (fun p : P => (check ((p.1.1.2/8).unpair.1::p.1.1.1) (p.1.1.2/8).unpair.2).bind (fun a =>
      (p.1.2.getD 0 none).bind (fun b => PolicyAbstraction.abstractionCode pol (typeLevel (p.1.1.2/8).unpair.1) (typeLevel a) b))) := by
      apply Computable.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.to_comp.comp
        (((Primrec.list_cons.comp hl' (Primrec.fst.comp hs)).pair hr').to_comp))
      have h1 : Primrec (fun q : P×Nat => typeLevel (q.1.1.1.2/8).unpair.1) :=
        (level.comp hl').comp Primrec.fst
      have h2 : Primrec (fun q : P×Nat => typeLevel q.2) := level.comp Primrec.snd
      have h3 : Primrec (fun q : P×Nat => q.1.1.2.getD 0 none) := (hg 0).comp Primrec.fst
      exact Computable.comp
        (f := fun q : Nat×Nat×Option (List Nat) => q.2.2.bind (fun b => PolicyAbstraction.abstractionCode pol q.1 q.2.1 b))
        (g := fun q : P×Nat => (typeLevel (q.1.1.1.2/8).unpair.1,typeLevel q.2,q.1.1.2.getD 0 none))
        (PolicyAssignmentBasePrograms.lamBind pol hpol) (h1.pair (h2.pair h3)).to_comp
    have hprime : Computable (fun p : P => PolicyAssignment.primeCode pol (p.1.1.2%8) (p.1.1.2/8) (typeLevel p.2)) :=
      Computable.comp (f := fun q : Nat×Nat×Nat => PolicyAssignment.primeCode pol q.1 q.2.1 q.2.2)
        (g := fun p : P => (p.1.1.2%8,p.1.1.2/8,typeLevel p.2))
        (PolicyAssignmentBasePrograms.prime pol hpol) (ht'.pair (hp'.pair (level.comp Primrec.snd))).to_comp
    exact PolicyAbstractionCoordinatePrograms.choose (Primrec.nat_lt.comp ht' (Primrec.const 5)) hprime
      (PolicyAbstractionCoordinatePrograms.choose ((ht 5).comp hs) happ
        (PolicyAbstractionCoordinatePrograms.choose ((ht 6).comp hs) hlam (Computable.const none)))
  have ha : Computable (fun x : S × List (Option (List Nat)) => assemble x.1 x.2) :=
    Computable.option_some.comp
      (Computable.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.to_comp.comp Computable.fst) hf.to₂)
  apply ComputableRankedProof.ranked S (Option (List Nat))
    (fun s => PolicyAssignment.assignmentCode pol s.1 s.2) (fun s => s.2) children assemble Primrec.snd hc ha
  · intro s t hmem
    change t.2 < s.2
    by_cases h5 : s.2%8=5
    · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : s.2%8=6
      · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hmem
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hmem
  · intro s
    conv_rhs => rw [PolicyAssignment.assignmentCode]
    have ht : s.2%8=0 ∨ s.2%8=1 ∨ s.2%8=2 ∨ s.2%8=3 ∨ s.2%8=4 ∨ s.2%8=5 ∨ s.2%8=6 ∨ s.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;> simp [children,assemble,finish,h,Option.bind_assoc]

end LogicLineages.StandardControlCurrent.PolicyAssignmentRunPrograms
