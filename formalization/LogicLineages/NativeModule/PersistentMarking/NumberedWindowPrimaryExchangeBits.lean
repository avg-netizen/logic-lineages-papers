module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchange
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTypingBitsChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeBits
open NumberedWindowSyntax NumberedWindowLiteralEquality
open NumberedWindowHeadEnumerationTargets (headBit)
open NumberedWindowTypingBits (windowBit binderLookup)

/-- The runtime equality used only for actual literal base permutations. -/
def literalDecEq (Q R : NTerm) : Decidable (Q = R) :=
  if h : termEq Q R = true
  then isTrue ((NumberedWindowTypingBitsChecks.exact_LiteralTermEquality Q R).mp h)
  else isFalse (fun e => h ((NumberedWindowTypingBitsChecks.exact_LiteralTermEquality Q R).mpr e))

def permutationBit (bs cs : NArgs) : Bool :=
  letI : DecidableEq NTerm := literalDecEq
  decide (bs.toList.Perm cs.toList)

def headPairBit (S : Spine.Signature) (K : List Ty) (f g : Head) : Bool :=
  headBit S K f && headBit S K g && decide (Spine.classRank S f = Spine.classRank S g)

mutual
def exchangeBit (S : Spine.Signature) (K : List Ty) : NTerm → NTerm → Bool
  | .ordinary f bs, .ordinary g cs =>
    (headPairBit S K f g && decide (f.result = g.result) && permutationBit bs cs) ||
      (decide (f = g) && argsExchangeBit S K bs cs)
  | .numbered f σ k bs es, .numbered g τ j cs ds =>
    decide (σ = τ) && decide (k = j) &&
      ((headPairBit S K f g && permutationBit bs cs && argsEq es ds) ||
        (decide (f = g) && ((argsExchangeBit S K bs cs && argsEq es ds) ||
          (argsEq bs cs && argsExchangeBit S K es ds))))
  | .lam σ Q, .lam τ R => decide (σ = τ) && exchangeBit S K Q R
  | .auxApp σ τ Q A, .auxApp ρ υ R B =>
    decide (σ = ρ) && decide (τ = υ) &&
      ((exchangeBit S K Q R && termEq A B) || (termEq Q R && exchangeBit S K A B))
  | _, _ => false

def argsExchangeBit (S : Spine.Signature) (K : List Ty) : NArgs → NArgs → Bool
  | .cons Q qs, .cons R rs =>
    (exchangeBit S K Q R && argsEq qs rs) || (termEq Q R && argsExchangeBit S K qs rs)
  | _, _ => false
end

def windowExchangeBit (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty)
    (Q R : NTerm) : Bool :=
  exchangeBit S K Q R && windowBit S K C τ Q && windowBit S K C τ R

def finiteExchangeBit (S : Spine.Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (Q R : NTerm) : Bool :=
  windowExchangeBit S K (binderLookup Γ) τ Q R

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeBits
