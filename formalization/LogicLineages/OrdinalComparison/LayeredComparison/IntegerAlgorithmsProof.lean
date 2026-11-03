module
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsTargets
public import Mathlib.Tactic.Ring
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof

private theorem encode_split (z:Int):
    Encodable.encode (Equiv.intEquivNatSumNat z)=Encodable.encode z:=by
  cases z <;> rfl
private theorem split_primitive : Primrec Equiv.intEquivNatSumNat := by
  apply Primrec.encode_iff.mp
  apply (Primrec.encode:Primrec (fun z:Int=>Encodable.encode z)).of_eq
  intro z
  exact (encode_split z).symm
private theorem join_primitive : Primrec Equiv.intEquivNatSumNat.symm := by
  apply Primrec.encode_iff.mp
  apply (Primrec.encode:Primrec (fun s:Nat⊕Nat=>Encodable.encode s)).of_eq
  intro s
  have h:=encode_split (Equiv.intEquivNatSumNat.symm s)
  simpa only [Equiv.apply_symm_apply] using h

theorem ofNat_primitive : Primrec (fun n:Nat=>(n:Int)) :=
  join_primitive.comp Primrec.sumInl
private theorem negSucc_primitive : Primrec Int.negSucc :=
  join_primitive.comp Primrec.sumInr

private def posPart (z:Int):Nat:=match z with| .ofNat n=>n|.negSucc _=>0
private def negPart (z:Int):Nat:=match z with| .ofNat _=>0|.negSucc n=>n+1
private theorem pos_primitive : Primrec posPart := by
  apply (Primrec.sumCasesOn split_primitive Primrec.snd.to₂ (Primrec.const 0).to₂).of_eq
  intro z
  cases z <;> rfl
private theorem neg_primitive : Primrec negPart := by
  apply (Primrec.sumCasesOn split_primitive (Primrec.const 0).to₂ (Primrec.succ.comp Primrec.snd).to₂).of_eq
  intro z
  cases z <;> rfl
private theorem parts (z:Int):z=(posPart z:Int)-(negPart z:Int):=by
  cases z <;> simp [posPart,negPart,Int.negSucc_eq]

theorem negate_primitive : Primrec (fun z:Int=>-z) := by
  have hp:Primrec (fun n:Nat=>if n=0 then (0:Int) else Int.negSucc (n-1)):=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
      (negSucc_primitive.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
  apply (Primrec.sumCasesOn split_primitive (hp.comp Primrec.snd).to₂
    (ofNat_primitive.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq
  intro z
  cases z with
  | ofNat n=>
    change (if n=0 then (0:Int) else Int.negSucc (n-1))= -Int.ofNat n
    cases n <;> rfl
  | negSucc n=>rfl

private def difference (a b:Nat):Int:=if b≤a then ((a-b:Nat):Int) else -((b-a:Nat):Int)
private theorem difference_primitive : Primrec₂ difference :=
  Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst) (ofNat_primitive.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (negate_primitive.comp (ofNat_primitive.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)))
private theorem difference_value (a b:Nat):difference a b=(a:Int)-(b:Int):=by
  unfold difference
  split <;> omega

theorem add_primitive : Primrec₂ (fun a b:Int=>a+b) := by
  have hpos:Primrec (fun p:Int×Int=>posPart p.1+posPart p.2):=
    Primrec.nat_add.comp (pos_primitive.comp Primrec.fst) (pos_primitive.comp Primrec.snd)
  have hneg:Primrec (fun p:Int×Int=>negPart p.1+negPart p.2):=
    Primrec.nat_add.comp (neg_primitive.comp Primrec.fst) (neg_primitive.comp Primrec.snd)
  apply (difference_primitive.comp hpos hneg).of_eq
  intro p
  rw [difference_value,Nat.cast_add,Nat.cast_add]
  change (posPart p.1:Int)+(posPart p.2:Int)-((negPart p.1:Int)+(negPart p.2:Int))=p.1+p.2
  have h₁:=parts p.1
  have h₂:=parts p.2
  omega

theorem mul_primitive : Primrec₂ (fun a b:Int=>a*b) := by
  have hp₁:=pos_primitive.comp (Primrec.fst:Primrec (fun p:Int×Int=>p.1))
  have hp₂:=pos_primitive.comp (Primrec.snd:Primrec (fun p:Int×Int=>p.2))
  have hn₁:=neg_primitive.comp (Primrec.fst:Primrec (fun p:Int×Int=>p.1))
  have hn₂:=neg_primitive.comp (Primrec.snd:Primrec (fun p:Int×Int=>p.2))
  have hpos:=Primrec.nat_add.comp (Primrec.nat_mul.comp hp₁ hp₂) (Primrec.nat_mul.comp hn₁ hn₂)
  have hneg:=Primrec.nat_add.comp (Primrec.nat_mul.comp hp₁ hn₂) (Primrec.nat_mul.comp hn₁ hp₂)
  apply (difference_primitive.comp hpos hneg).of_eq
  intro p
  rw [difference_value,Nat.cast_add,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul]
  calc
    _=((posPart p.1:Int)-(negPart p.1:Int))*((posPart p.2:Int)-(negPart p.2:Int)):=by ring
    _=p.1*p.2:=by rw [←parts p.1,←parts p.2]

theorem abs_primitive : Primrec Int.natAbs := by
  apply (Primrec.nat_add.comp pos_primitive neg_primitive).of_eq
  intro z
  cases z <;> simp [posPart,negPart]

theorem sign_primitive : Primrec Int.sign := by
  have hp:Primrec (fun n:Nat=>if n=0 then (0:Int) else 1):=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0) (Primrec.const 1)
  apply (Primrec.sumCasesOn split_primitive (hp.comp Primrec.snd).to₂ (Primrec.const (-1)).to₂).of_eq
  intro z
  cases z with
  | ofNat n=>
    change (if n=0 then (0:Int) else 1)=Int.sign (Int.ofNat n)
    cases n <;> rfl
  | negSucc n=>rfl

theorem signedArithmetic : Targets.SignedArithmetic :=
  ⟨ofNat_primitive,negate_primitive,add_primitive,mul_primitive,abs_primitive,sign_primitive⟩
end LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
