module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationDomainProof
public import LogicLineages.NativeModule.PersistentMarking.SpineShiftProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationShiftProof
open NumberedWindowSyntax NumberedWindowDomain

mutual
theorem typed (C D : Spine.BoundContext) (Q : NTerm) (τ : Ty) (a c : Nat)
    (h : Typed C Q τ) (hc : Spine.ShiftCompatible a c C D) :
    Typed D (shift a c Q) τ := by
  cases h with
  | free => exact .free
  | bound hi => exact .bound (hc _ _ hi)
  | lam hb => exact .lam (typed _ _ _ _ _ _ hb (SpineShiftProof.compatiblePush _ _ _ _ hc _))
  | bottom => exact .bottom
  | ordinary hb => exact .ordinary (baseTyped _ _ _ _ _ _ hb hc)
  | numbered hb he => exact .numbered (baseTyped _ _ _ _ _ _ hb hc) (extrasTyped _ _ _ _ _ he hc)
  | auxApp hq ha => exact .auxApp (typed _ _ _ _ _ _ hq hc) (typed _ _ _ _ _ _ ha hc)
termination_by sizeOf Q

theorem baseTyped (C D : Spine.BoundContext) (As : NArgs) (types : List Ty) (a c : Nat)
    (h : BaseTyped C As types) (hc : Spine.ShiftCompatible a c C D) :
    BaseTyped D (shiftArgs a c As) types := by
  cases h with
  | nil => exact .nil
  | cons hq ht => exact .cons (typed _ _ _ _ _ _ hq hc) (baseTyped _ _ _ _ _ _ ht hc)
termination_by sizeOf As

theorem extrasTyped (C D : Spine.BoundContext) (As : NArgs) (a c : Nat)
    (h : ExtrasTyped C As) (hc : Spine.ShiftCompatible a c C D) :
    ExtrasTyped D (shiftArgs a c As) := by
  cases h with
  | nil => exact .nil
  | cons hq ht => exact .cons (typed _ _ _ _ _ _ hq hc) (extrasTyped _ _ _ _ _ ht hc)
termination_by sizeOf As
end

mutual
theorem shape (Q : NTerm) (a c : Nat) :
    (shift a c Q).type = Q.type ∧ support (shift a c Q) = support Q ∧ heads (shift a c Q) = heads Q := by
  cases Q with
  | free σ x => exact ⟨rfl,rfl,rfl⟩
  | bound σ i => exact ⟨rfl,rfl,rfl⟩
  | lam σ q =>
    obtain ⟨ht,hs,hh⟩ := shape q a (c+1)
    exact ⟨by simp only [shift,NTerm.type,ht],by simp only [shift,support,ht,hs],hh⟩
  | bottom τ => exact ⟨rfl,rfl,rfl⟩
  | ordinary f bs =>
    obtain ⟨hs,hh⟩ := argsShape bs a c
    exact ⟨rfl,by simp only [shift,support,hs],by simp only [shift,heads,hh]⟩
  | numbered f τ k bs es =>
    obtain ⟨hbs,hbh⟩ := argsShape bs a c
    obtain ⟨hes,heh⟩ := argsShape es a c
    exact ⟨rfl,by simp only [shift,support,hbs,hes],by simp only [shift,heads,hbh,heh]⟩
  | auxApp σ τ q b =>
    obtain ⟨_,hqs,hqh⟩ := shape q a c
    obtain ⟨_,hbs,hbh⟩ := shape b a c
    exact ⟨rfl,by simp only [shift,support,hqs,hbs],by simp only [shift,heads,hqh,hbh]⟩
termination_by sizeOf Q

theorem argsShape (As : NArgs) (a c : Nat) :
    argsSupport (shiftArgs a c As) = argsSupport As ∧ argsHeads (shiftArgs a c As) = argsHeads As := by
  cases As with
  | nil => exact ⟨rfl,rfl⟩
  | cons q tail =>
    obtain ⟨_,hqs,hqh⟩ := shape q a c
    obtain ⟨hts,hth⟩ := argsShape tail a c
    exact ⟨by simp only [shiftArgs,argsSupport,hqs,hts],by simp only [shiftArgs,argsHeads,hqh,hth]⟩
termination_by sizeOf As
end

end LogicLineages.PersistentMarking.NumberedWindowApplicationShiftProof
