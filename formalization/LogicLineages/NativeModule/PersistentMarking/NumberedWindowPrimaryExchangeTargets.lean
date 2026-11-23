module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimaryExchange NumberedWindowPrimaryExchangeBits
open NumberedWindowTypingBits (annotationList)

def HeadPairReflection : Prop := ∀ S K f g,
  headPairBit S K f g = true ↔ AllowedHeadPair S K f g

def TermExchangeReflection : Prop := ∀ S K Q R,
  exchangeBit S K Q R = true ↔ ExchangeShape S K Q R

def ArgsExchangeReflection : Prop := ∀ S K qs rs,
  argsExchangeBit S K qs rs = true ↔ ArgsExchangeShape S K qs rs

def WindowExchangeReflection : Prop := ∀ S K C τ Q R,
  windowExchangeBit S K C τ Q R = true ↔ WindowExchange S K C τ Q R

def FiniteExchangeReflection : Prop := ∀ S K Γ τ Q R,
  finiteExchangeBit S K Γ τ Q R = true ↔
    WindowExchange S K (Spine.BoundContext.«prefix» Γ Spine.EmptyContext) τ Q R

def ExchangePreservesAnnotations : Prop :=
  (∀ S K Q R, ExchangeShape S K Q R → Q.type = R.type) ∧
  (∀ S K qs rs, ArgsExchangeShape S K qs rs → annotationList qs = annotationList rs)

def ExchangeSymmetric : Prop :=
  (∀ S K Q R, ExchangeShape S K Q R → ExchangeShape S K R Q) ∧
  (∀ S K qs rs, ArgsExchangeShape S K qs rs → ArgsExchangeShape S K rs qs)

def WindowExchangeSound : Prop := ∀ S K C τ Q R,
  WindowExchange S K C τ Q R → Primary S K C τ Q R

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeTargets
