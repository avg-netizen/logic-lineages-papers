module
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityParityProof
public import LogicLineages.OrdinalComparison.SourceControlNonperiodicityFibersProof
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicity.Proof
open SourceControlNonperiodicity (fiberBase fiberPoint)
open SourceControlNonperiodicity.Proof (fiber_point_above exactValuationFibers fiber_base_primitive)
open SourceBlankMachineSimulation

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
    boundedH (e,fiberBase N b e) = true ↔ Halts e := by
  constructor
  · intro hb
    exact (SourceBlankMachineSimulation.Proof.monotoneHalting.2 e).2 ⟨_,hb⟩
  · intro hh
    obtain ⟨k,hk⟩ := (SourceBlankMachineSimulation.Proof.monotoneHalting.2 e).mp hh
    have hpoint := (exactValuationFibers.2 N b p e k hp)
    have hbnd := SourceBlankMachineSimulation.Proof.monotoneHalting.1 e k (fiberPoint N b p e k) hpoint.2.2.2 hk
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
  have hbase : Primrec (fun e : Nat => fiberBase N b e) :=
    fiber_base_primitive.comp ((Primrec.const N).pair ((Primrec.const b).pair Primrec.id))
  have htest : Primrec (fun e : Nat => boundedH (e,fiberBase N b e)) :=
    SourceBlankMachineSimulation.Proof.effectiveEnumeration.2.2.comp (Primrec.id.pair hbase)
  have hdec : ComputablePred (fun e : Nat => boundedH (e,fiberBase N b e) = true) :=
    (Primrec.eq.comp htest (Primrec.const true)).computablePred
  apply SourceBlankHaltingReduction.Proof.blankHaltingUndecidable
  exact hdec.of_eq (base_halting b N p hp hperiod)
end LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicity.Proof
