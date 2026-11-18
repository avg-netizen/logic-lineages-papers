module
public import LogicLineages.StandardControlCurrent.NumericalKernelBaseProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NumericalKernelProof
open OrdinalComparison NumericalKernel

theorem signed_agreement (d c t : Nat) (hd : 1 ≤ d) (ht : c+d+1 ≤ t) (j : Int) :
    signed d c j t = rawSignedKernelValue d c j t := by
  unfold signed rawSignedKernelValue
  rw [depth_agreement d c t hd ht j]

theorem recurrence : NumericalKernelTargets.Recurrences := by
  constructor
  · intro n c t ht
    dsimp only
    have hp := padded (n+2) c t (by omega) (by omega)
    have he := padded (n+2) (c+n+2) t (by omega) (by omega)
    have hself : t ≤ value (n+2) (c+n+2) t :=
      iterate_self_le (fun x => (self_lt_Phi x).le) _ t
    have hc := padded (n+1) c (value (n+2) (c+n+2) t) (by omega) (by omega)
    have h := FiniteKernelRecursion.block n c t ht
    dsimp only at h
    rw [hp.1,hp.2,hc.1,hc.2,he.1,he.2]
    exact h
  · intro n c j hj t ht
    dsimp only
    have hdom : c+2*(n+2)+1 ≤ t := (Nat.le_max_left _ _).trans ht
    have he := padded (n+2) (c+n+2) t (by omega) (by omega)
    have hself : t ≤ value (n+2) (c+n+2) t :=
      iterate_self_le (fun x => (self_lt_Phi x).le) _ t
    have h := FiniteKernelRecursion.signed_block n c j hj t ht
    dsimp only at h
    rw [depth_agreement (n+2) c t (by omega) (by omega) j,
      depth_agreement (n+1) c (value (n+2) (c+n+2) t) (by omega) (by omega) j,
      signed_agreement (n+2) c t (by omega) (by omega) j,
      signed_agreement (n+1) c (value (n+2) (c+n+2) t) (by omega) (by omega) j,
      he.2]
    exact h
end LogicLineages.StandardControlCurrent.NumericalKernelProof
