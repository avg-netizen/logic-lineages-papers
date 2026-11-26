import LogicLineages.PersistentMarking.NumberedWindowExternalMultisetClosureTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalIDOperatorChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticOccurrencePartitionChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExternalMultisetUnionProof
open Spine NumberedWindowArithmeticFields NumberedWindowArithmeticFieldsProof
open NumberedWindowArithmeticDirectMultisetTargets NumberedWindowArithmeticDirectCodeTargets
open NumberedWindowExternalIDOperators NumberedWindowExternalMultisetClosureTargets

private theorem fields_injective {xs ys : List Nat} (h : encodeFields xs = encodeFields ys) :
    xs = ys := by
  have eq := congrArg decodeFields h
  simpa only [fieldsRound, Option.some.injEq] using eq

private theorem accFromCode {S K n} (h : Acc (fun d s => DirectAtCode S K s d) n) :
    ∀ xs : List Nat, encodeFields xs = n → Acc (fun d s => AddressDirect S K s d) xs := by
  induction h with
  | intro n _ ih =>
    intro xs hx
    constructor
    intro ys step
    exact ih (encodeFields ys) ⟨xs,ys,hx,rfl,step⟩ ys rfl

private theorem accToCode {S K xs} (h : Acc (fun d s => AddressDirect S K s d) xs) :
    Acc (fun d s => DirectAtCode S K s d) (encodeFields xs) := by
  induction h with
  | intro xs _ ih =>
    constructor
    rintro n ⟨before,after,hb,ha,step⟩
    have eq := fields_injective hb
    subst before
    subst n
    exact ih after step

/-- The external coded J is exactly the original typed list domain and
accessibility for an actual strict occurrence replacement on lists. -/
theorem coded_iff (S : Signature) (K : List Ty) (xs : List Nat) :
    Least (multisetStep S K) (encodeFields xs) ↔
      TypedAddressList S K xs ∧ Acc (fun d s => AddressDirect S K s d) xs := by
  rw [(NumberedWindowExternalIDOperatorChecks.exact_ActualGuardedAccessibilitySemantics
    S K (encodeFields xs)).2]
  constructor
  · rintro ⟨⟨ys,hy,typed⟩,acc⟩
    obtain rfl := fields_injective hy
    exact ⟨typed,accFromCode acc xs rfl⟩
  · rintro ⟨typed,acc⟩
    exact ⟨⟨xs,rfl,typed⟩,accToCode acc⟩

private theorem permAcc {S K xs ys} (h : Acc (fun d s => AddressDirect S K s d) xs)
    (p : xs.Perm ys) : Acc (fun d s => AddressDirect S K s d) ys := by
  constructor
  intro z hz
  exact h.inv ((NumberedWindowArithmeticDirectMultisetDomain.permutations S K xs ys z z
    p (List.Perm.refl _)).mpr hz)

private theorem unionAcc {S K xs} (hx : Acc (fun d s => AddressDirect S K s d) xs) :
    ∀ ys : List Nat, Acc (fun d s => AddressDirect S K s d) ys →
      Acc (fun d s => AddressDirect S K s d) (xs ++ ys) := by
  induction hx with
  | intro xs _ outer =>
    intro ys hy
    induction hy with
    | intro ys prev inner =>
      constructor
      intro target step
      obtain ⟨l,r,order,split⟩ :=
        NumberedWindowArithmeticOccurrencePartitionChecks.exact_DirectAddressUnionSplit
          S K xs ys target step
      apply permAcc _ order.symm
      rcases split with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · apply outer l hl r
        rcases hr with same | strict
        · exact permAcc (Acc.intro ys prev) same
        · exact prev r strict
      · exact permAcc (inner r hr) (hl.append (List.Perm.refl _))

theorem union : ExternalJUnion := by
  intro S K xs ys hx hy
  obtain ⟨tx,ax⟩ := (coded_iff S K xs).mp hx
  obtain ⟨ty,ay⟩ := (coded_iff S K ys).mp hy
  apply (coded_iff S K (xs ++ ys)).mpr
  refine ⟨?_,unionAcc ax ys ay⟩
  intro a ha
  exact (List.mem_append.mp ha).elim (tx a) (ty a)

end LogicLineages.PersistentMarking.NumberedWindowExternalMultisetUnionProof
