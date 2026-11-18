import LogicLineages.PersistentMarking.GraftingProof
import LogicLineages.PersistentMarking.NativeTypingProof
namespace LogicLineages.PersistentMarking.NativeBetaSupport
open Spine NameBridge TypeSupport Grafting

theorem realize (σ : Ty) (x : Nat) (a body : Expr) (hf : freeOccurs (σ,x) body = false) :
    freeSub (singleMap σ x a) 0 (openBody σ x body) = substitute (.cons a .nil) 0 body := by
  have hc := FreeCompositionProof.composition (singleMap σ x a) (.cons (.free σ x) .nil) 0 body
  have ha := RefinementCallMapProof.absent σ x a 1 body hf
  simpa only [openBody,freeSubArgs,freeSub,singleMap,ite_true,SubstitutionProof.shiftZero,
    Args.length,Nat.zero_add,ha] using hc

def Slot (Γ : BoundContext) (d : Nat) (σ : Ty) : Prop := ∀ i δ, Γ i = some δ → i ≤ d ∧ (i = d → δ = σ)

theorem slotPush {Γ : BoundContext} {d : Nat} {σ : Ty} (h : Slot Γ d σ) (τ : Ty) : Slot (Γ.push τ) (d+1) σ := by
  intro i δ hi
  cases i with
  | zero => exact ⟨by omega,by intro he; omega⟩
  | succ i =>
    have hh := h i δ hi
    exact ⟨by omega,fun he => hh.2 (by omega)⟩

mutual
 theorem openingSupport (Γ : BoundContext) (d : Nat) (σ : Ty) (x : Nat) (hc : Slot Γ d σ)
    (q : Expr) (τ : Ty) (ht : Typed Γ q τ) :
    (substitute (.cons (.free σ x) .nil) d q).type = q.type ∧
    support (substitute (.cons (.free σ x) .nil) d q) = support q := by
  cases q with
  | free δ y => exact ⟨rfl,rfl⟩
  | bound δ i =>
    cases ht with
    | bound hi =>
      have hh := hc i _ hi
      by_cases hl : i < d
      · simp only [substitute,hl,if_true]; exact ⟨rfl,rfl⟩
      · have he : i = d := by omega
        have hδ := hh.2 he
        subst i
        subst δ
        simp [substitute,Args.get,shift,Expr.type,support]
  | lam δ q =>
    cases ht with
    | lam hq =>
      have hh := openingSupport (Γ.push δ) (d+1) σ x (slotPush hc δ) q _ hq
      simp only [substitute,Expr.type,support,hh.1,hh.2]
      exact ⟨rfl,rfl⟩
  | head f qs =>
    cases ht with
    | head hqs =>
      exact ⟨rfl,congrArg (fun xs => subtypes f.result ++ xs) (openingBaseSupport Γ d σ x hc qs _ hqs)⟩
  | marked f τ qs es =>
    cases ht with
    | marked hqs hes =>
      simp only [substitute,Expr.type,support,openingBaseSupport Γ d σ x hc qs _ hqs,openingExtrasSupport Γ d σ x hc es hes]
      exact ⟨rfl,rfl⟩
 termination_by sizeOf q
 theorem openingBaseSupport (Γ : BoundContext) (d : Nat) (σ : Ty) (x : Nat) (hc : Slot Γ d σ)
    (qs : Args) (types : List Ty) (ht : BaseTyped Γ qs types) :
    supportArgs (substituteArgs (.cons (.free σ x) .nil) d qs) = supportArgs qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      simp only [substituteArgs,supportArgs,(openingSupport Γ d σ x hc q _ hq).2,openingBaseSupport Γ d σ x hc qs _ hqs]
 termination_by sizeOf qs
 theorem openingExtrasSupport (Γ : BoundContext) (d : Nat) (σ : Ty) (x : Nat) (hc : Slot Γ d σ)
    (qs : Args) (ht : ExtrasTyped Γ qs) :
    supportArgs (substituteArgs (.cons (.free σ x) .nil) d qs) = supportArgs qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      simp only [substituteArgs,supportArgs,(openingSupport Γ d σ x hc q _ hq).2,openingExtrasSupport Γ d σ x hc qs hqs]
 termination_by sizeOf qs
end

theorem openingSupportExact (σ τ : Ty) (x : Nat) (body : Expr) (ht : Typed (EmptyContext.push σ) body τ) :
    support (openBody σ x body) = support body := by
  have hc : Slot (EmptyContext.push σ) 0 σ := by
    intro i δ hi
    cases i with
    | zero => have hh : σ = δ := Option.some.inj hi; exact ⟨Nat.le_refl _,fun _ => hh.symm⟩
    | succ i => simp [BoundContext.push,EmptyContext] at hi
  exact (openingSupport (EmptyContext.push σ) 0 σ x hc body τ ht).2
end LogicLineages.PersistentMarking.NativeBetaSupport
