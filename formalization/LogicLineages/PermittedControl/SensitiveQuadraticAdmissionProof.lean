module
public import LogicLineages.PermittedControl.SensitiveAdmissionProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem quadraticUnitAdmission : Targets.QuadraticUnitAdmission := by
  intro f B mu nu P r A A' R t hs
  have hs0 := hs
  rcases hs with ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,h2,hdiv,hr,hrd,
    hR,hmuR,hnuR,hPR,haR,ht,hpart,hpart',hnorm,hnorm',hcd⟩
  rcases sensitive_admission f B mu nu P 2 r A A' R t hs0 with hdiverged | ⟨i,hi,hj,hstop⟩
  · exact Or.inl hdiverged
  let Ai := (descentWith f)^[i] A
  let Ai' := (descentWith f)^[i] A'
  let E := f^[i] t
  have hstep := sensitive_top_step f B mu nu P 2 Ai Ai' R E hstop
  by_cases heq : actualLimitPart (descentWith f Ai-mu)=actualLimitPart (descentWith f Ai'-nu)
  · right
    have hexception := (quadraticUnitTop f B mu nu P Ai Ai' R E hstop).mp heq
    refine ⟨hexception.1,hexception.2,?_⟩
    let X := f E-relativeProfile mu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P
    have hEt := iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t
    have hlarge := sensitive_tail_large R B t ht
    have hu := (G_large E).trans ((selected_threshold_admissible f B hf).2 E)
    have hcR := (relativePrefixNorm mu (Ordinal.log Ordinal.omega0 P) hmu).2.2.trans hmuR
    have hX : 2 ≤ X := by dsimp only [X]; omega
    have hform : actualLimitPart (descentWith f Ai-mu)=P+Ordinal.omega0*((X/2 : Nat) : Ordinal) := by
      rw [hstep.1,actualOmegaSquaredMaximum X hX,← add_assoc]
      have hq : 0 < ((X/2 : Nat) : Ordinal) := by exact_mod_cast (show 0 < X/2 by omega)
      exact limitPart_tail _ (Ordinal.isSuccLimit_add P
        (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hq)) _
    have hpow : Ordinal.omega0^(2 : Ordinal.{0})=Ordinal.omega0^(2 : Nat) := by
      simpa using Ordinal.opow_natCast Ordinal.omega0 2
    refine ⟨i,X/2,?_,?_,?_,?_,?_,?_⟩
    · simpa only [← hpow] using hi
    · simpa only [← hpow] using hj
    · rw [Function.iterate_succ_apply',Function.iterate_succ_apply' f i t]
      exact hstep.2.2.1
    · rw [Function.iterate_succ_apply',Function.iterate_succ_apply' f i t]
      exact hstep.2.2.2.1
    · rw [Function.iterate_succ_apply']
      exact hform
    · rw [Function.iterate_succ_apply']
      exact heq.symm.trans hform
  · left
    apply sensitive_orient f B mu nu P 2 r A A' R t hs0
    refine ⟨i+1,?_,?_,?_⟩
    · rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      exact heq
    · rw [Function.iterate_succ_apply']
      exact hstep.2.2.2.2.1
    · rw [Function.iterate_succ_apply']
      exact hstep.2.2.2.2.2

end LogicLineages.PermittedControl
