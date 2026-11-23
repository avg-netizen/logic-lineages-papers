module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowFiniteSaturation
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimarySequenceChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryCoverChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryClassList
open NumberedWindowSyntax NumberedWindowPrimaryCoverSyntax
open NumberedWindowPrimaryExchangeBits NumberedWindowLiteralEquality
open NumberedWindowTypingBits (binderLookup)
open NumberedWindowFiniteSaturation

/- The executable list used in the finite context is built on the actual
source-selected cover, retaining the genuine already checked typed
elementary exchange bit. Unrelated candidates may be in the cover,
but enter the result only through genuine reachable exchanges. -/
def classList (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty)
    (Q : NTerm) : List NTerm :=
  saturate (cover S K Q) termEq (windowExchangeBit S K C τ) Q

def finiteClassList (S : Spine.Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (Q : NTerm) : List NTerm :=
  classList S K (binderLookup Γ) τ Q

def primaryBit (S : Spine.Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (Q R : NTerm) : Bool :=
  (finiteClassList S K Γ τ Q).any (termEq R)

end LogicLineages.PersistentMarking.NumberedWindowPrimaryClassList
