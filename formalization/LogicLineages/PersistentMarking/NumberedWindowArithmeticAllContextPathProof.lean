import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextPathProof
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticPathCheckChecks
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticAllContextTargets

theorem positive : ExactAddressPositivePath := by
  intro S K src dst hk
  constructor
  · rintro ⟨c,h⟩
    cases hs : decodeAddress src with
    | none => simp [addressRSBit,hs] at h
    | some a =>
      cases hd : decodeAddress dst with
      | none => simp [addressRSBit,hs,hd] at h
      | some b =>
        rcases a with ⟨Γ,τ,i⟩
        rcases b with ⟨Δ,σ,j⟩
        simp only [addressRSBit,hs,hd,Bool.and_eq_true,decide_eq_true_eq] at h
        obtain ⟨⟨eΓ,eτ⟩,hp⟩ := h
        change Γ = Δ at eΓ
        change τ = σ at eτ
        subst Δ
        subst σ
        obtain ⟨x,y,hx,hy,hxy⟩ :=
          (exact_PositiveClassPathOnCodes S K Γ τ i j hk).mp ⟨c,hp⟩
        exact ⟨Γ,τ,i,j,x,y,read hs,read hd,hx,hy,hxy⟩
  · rintro ⟨Γ,τ,i,j,x,y,hs,hd,hx,hy,hxy⟩
    obtain ⟨c,h⟩ :=
      (exact_PositiveClassPathOnCodes S K Γ τ i j hk).mpr ⟨x,y,hx,hy,hxy⟩
    refine ⟨c,?_⟩
    simp only [addressRSBit,atCode hs,atCode hd,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨by simp,by simp⟩,h⟩

theorem domain : ActualAddressPathDomain := by
  intro S K src dst h
  obtain ⟨Γ,τ,i,j,x,y,hs,hd,hx,hy,_⟩ := h
  exact ⟨⟨Γ,τ,i,x,hs,hx⟩,⟨Γ,τ,j,y,hd,hy⟩⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextPathProof
