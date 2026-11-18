module
public import LogicLineages.PermittedControl.PureCertificateClockProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem pure_terminal_comparison (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu E A A' : Ordinal.{0}) (R t tau sigma : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hE : E < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hE2 : 2 ≤ E) (hR : 20 ≤ R) (hmuR : actualOrdinalNorm mu ≤ R)
    (hnuR : actualOrdinalNorm nu ≤ R) (hER : actualOrdinalNorm E ≤ R)
    (ht : thickBlockTail R B ≤ t) (hp : actualLimitPart A=mu+Ordinal.omega0^E)
    (hp' : actualLimitPart A'=nu+Ordinal.omega0^E) (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hagree : ∀ e : Ordinal.{0}, 2 ≤ e → e < E → relativeProfile mu e=relativeProfile nu e)
    (hHit : FirstEntry f A mu tau) (hHit' : FirstEntry f A' nu sigma) :
    compare (entryNormAt f A tau) (entryNormAt f A' sigma)=
      compare ((relativeProfile nu 1+1)/2) ((relativeProfile mu 1+1)/2) := by
  have h2 : (2 : Ordinal.{0}) < epsilonZero := by simpa using finiteCoefficient_below 0 2
  have hN2 : actualOrdinalNorm (2 : Ordinal.{0})=2 := by simpa using actualFiniteHeadNorm 0 2
  obtain ⟨i,hi,hi',hiN,hiN'⟩ := actualProfileBandReturn f B hf mu nu E 2 A A' R t
    hmu hnu hE h2 hA hA' hmud hnud (by norm_num) hE2 hR hmuR hnuR hER (by omega)
    ht hp hp' hn hn' hagree
  have hgrow := iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t
  have hhead := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (by norm_num : (2 : Ordinal.{0}) ≠ 0)
  have hlim := (interval_iff_limitPart _ (mu+Ordinal.omega0^(2 : Ordinal)) (Or.inr (Ordinal.isSuccLimit_add mu hhead))).mp ⟨hi.1,hi.2.1⟩
  have hlim' := (interval_iff_limitPart _ (nu+Ordinal.omega0^(2 : Ordinal)) (Or.inr (Ordinal.isSuccLimit_add nu hhead))).mp ⟨hi'.1,hi'.2.1⟩
  have hterm := actualTerminalSquareComparison f B hf mu nu _ _ R (f^[i] t) hmu hnu
    (trajectory_below f A hA i) (trajectory_below f A' hA' i) hmud hnud hR hmuR hnuR
    (ht.trans hgrow) hlim hlim' hiN hiN'
  let p := 1+(f (f^[i] t)-relativeProfile mu 1)/2
  let q := 1+(f (f^[i] t)-relativeProfile nu 1)/2
  have hc := compose_pure_entry f mu 2 A i p hA (by norm_num) hi hterm.1
  have hc' := compose_pure_entry f nu 2 A' i q hA' (by norm_num) hi' hterm.2.1
  have he := firstEntry_unique f A mu (i+p) tau hc hHit
  have he' := firstEntry_unique f A' nu (i+q) sigma hc' hHit'
  rw [←he,←he']
  simpa only [entryNormAt,Nat.add_comm i p,Nat.add_comm i q,Function.iterate_add_apply] using hterm.2.2

end LogicLineages.PermittedControl
