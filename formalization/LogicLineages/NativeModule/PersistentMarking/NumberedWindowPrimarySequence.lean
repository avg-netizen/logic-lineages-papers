module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequence
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimaryExchange

/-- One actual elementary shape with genuine typing at both ends in the
same C and result. The fixed original head guard is inside the shape;
no whole-window intermediate guard is presumed at this typed stage. -/
def TypedExchange (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty)
    (Q R : NTerm) : Prop :=
  ExchangeShape S K Q R ∧ Typed C Q τ ∧ Typed C R τ

def TypedArgsExchange (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (types : List Ty) (qs rs : NArgs) : Prop :=
  ArgsExchangeShape S K qs rs ∧ BaseTyped C qs types ∧ BaseTyped C rs types

/- These traces carry actual vertices in Type. In particular, the visit
list below is a function of the supplied sequence, not an assertion
about an erased Prop proof or a separately chosen witnessing path. -/
inductive TypedExchangeTrace (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (τ : Ty) : NTerm → NTerm → Type where
  | refl : Typed C Q τ → TypedExchangeTrace S K C τ Q Q
  | next : TypedExchange S K C τ Q R → TypedExchangeTrace S K C τ R T →
      TypedExchangeTrace S K C τ Q T

inductive TypedArgsExchangeTrace (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (types : List Ty) : NArgs → NArgs → Type where
  | refl : BaseTyped C qs types → TypedArgsExchangeTrace S K C types qs qs
  | next : TypedArgsExchange S K C types qs rs → TypedArgsExchangeTrace S K C types rs ts →
      TypedArgsExchangeTrace S K C types qs ts

inductive AdmittedExchangeTrace (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (τ : Ty) : NTerm → NTerm → Type where
  | refl : InWindow S K C τ Q → AdmittedExchangeTrace S K C τ Q Q
  | next : WindowExchange S K C τ Q R → AdmittedExchangeTrace S K C τ R T →
      AdmittedExchangeTrace S K C τ Q T

def typedVertices {S K C τ} {Q R : NTerm} (trace : TypedExchangeTrace S K C τ Q R) :
    List NTerm :=
  match trace with
  | .refl _ => [Q]
  | .next _ tail => Q :: typedVertices tail

def admittedVertices {S K C τ} {Q R : NTerm} (trace : AdmittedExchangeTrace S K C τ Q R) :
    List NTerm :=
  match trace with
  | .refl _ => [Q]
  | .next _ tail => Q :: admittedVertices tail

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequence
