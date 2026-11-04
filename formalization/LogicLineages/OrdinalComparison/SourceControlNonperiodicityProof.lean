module
public import LogicLineages.OrdinalComparison.SourceControlNonperiodicityParityProof
public import LogicLineages.OrdinalComparison.SourceControlNonperiodicityFibersProof
public import Mathlib.Computability.Halting

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Proof

private theorem periodic_multiples (b N p : Nat)
    (h : ∀ n : Nat, N ≤ n → gamma b (n+p)%2 = gamma b n%2)
    (n : Nat) (hn : N ≤ n) (k : Nat) :
    gamma b (n+k*p)%2 = gamma b n%2 := by
  induction k with
  | zero => simp only [zero_mul,add_zero]
  | succ k ih =>
    rw [Nat.succ_mul,← Nat.add_assoc,h (n+k*p) (by omega),ih]

private theorem periodic_fiber (b N p : Nat)
    (h : ∀ n : Nat, N ≤ n → gamma b (n+p)%2 = gamma b n%2)
    (e k : Nat) :
    gamma b (fiberPoint N b p e k)%2 = gamma b (fiberBase N b e)%2 := by
  have hb : N ≤ fiberBase N b e := by
    have h0 := fiber_point_above N b p e 0
    simp only [fiberPoint,zero_mul,add_zero] at h0
    omega
  have hm := periodic_multiples b N p h (fiberBase N b e) hb (k*2^(e+1))
  convert hm using 1 <;> congr 2
  unfold fiberPoint
  ring

private theorem base_halting (b N p : Nat) (hp : 0 < p)
    (h : ∀ n : Nat, N ≤ n → gamma b (n+p)%2 = gamma b n%2) (e : Nat) :
    boundedH (e,fiberBase N b e) = true ↔ (Nat.Partrec.Code.eval (program e) 0).Dom := by
  constructor
  · exact bounded_sound e (fiberBase N b e)
  · intro hh
    obtain ⟨k,hk⟩ := (halting_iff e).mp hh
    have hpoint := (exactValuationFibers.2 N b p e k hp)
    have hbnd := bounded_mono e k (fiberPoint N b p e k) hpoint.2.2.2 hk
    have hbase := exactValuationFibers.2 N b p e 0 hp
    simp only [fiberPoint,zero_mul,add_zero] at hbase
    have hp1 := parity_exact b (fiberPoint N b p e k) (by omega)
    have hp0 := parity_exact b (fiberBase N b e) (by omega)
    rw [hpoint.2.1,hbnd] at hp1
    rw [hbase.2.1] at hp0
    have hsame := periodic_fiber b N p h e k
    rw [hp1,hp0] at hsame
    cases hx : boundedH (e,fiberBase N b e) <;> simp_all

theorem nonEventualPeriodicity : Targets.NonEventualPeriodicity := by
  intro b
  rintro ⟨N,p,hp,hperiod⟩
  have hbase : Primrec (fun c : Nat.Partrec.Code => fiberBase N b (Encodable.encode c)) :=
    fiber_base_primitive.comp ((Primrec.const N).pair ((Primrec.const b).pair Primrec.encode))
  have htest : Primrec (fun c : Nat.Partrec.Code => boundedH
      (Encodable.encode c,fiberBase N b (Encodable.encode c))) :=
    bounded_primitive.comp (Primrec.encode.pair hbase)
  have hdec : ComputablePred (fun c : Nat.Partrec.Code => boundedH
      (Encodable.encode c,fiberBase N b (Encodable.encode c)) = true) :=
    (Primrec.eq.comp htest (Primrec.const true)).computablePred
  apply ComputablePred.halting_problem 0
  apply hdec.of_eq
  intro c
  simpa only [program_roundtrip] using base_halting b N p hp hperiod (Encodable.encode c)
end LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Proof
