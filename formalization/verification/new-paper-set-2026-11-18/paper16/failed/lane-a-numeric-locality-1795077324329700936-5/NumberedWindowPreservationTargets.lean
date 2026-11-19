import LogicLineages.PersistentMarking.NumberedWindowPrimary

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowPrimary

/-- Actual lexical-typed numerical trace. It does NOT assume initial
or intermediate type-window admission. The typed endpoint premises on
raw edges are not the stronger `WindowStep` guard. -/
inductive TypedTrace (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty) :
    NTerm → NTerm → Type where
  | done : Typed C q τ → TypedTrace S K C τ q q
  | raw : Typed C q τ → Typed C r τ → RawStep S K q r →
      TypedTrace S K C τ r t → TypedTrace S K C τ q t
  | equiv : Primary S K C τ q r →
      TypedTrace S K C τ r t → TypedTrace S K C τ q t

def vertices {S K C τ} {q t : NTerm} : TypedTrace S K C τ q t → List NTerm
  | .done _ => [q]
  | .raw _ _ _ tail => q :: vertices tail
  | .equiv _ tail => q :: vertices tail

/-- RawStep is only the printed rule-shape skeleton (especially Stat).
The typed result is an input, original window admissibility of that
result is the genuine conclusion. No successor support premise. -/
def RawTypedAdmissibility : Prop := ∀ S K C τ q r,
  DecisionSourceUniverse.Closed K →
  InWindow S K C τ q → Typed C r τ → RawStep S K q r →
  InWindow S K C τ r

def PrimaryAdmissibility : Prop := ∀ S K C τ q r,
  DecisionSourceUniverse.Closed K → Primary S K C τ q r →
  (InWindow S K C τ q ↔ InWindow S K C τ r)

def AllTypedTraceIntermediates : Prop := ∀ S K C τ q t,
  DecisionSourceUniverse.Closed K → InWindow S K C τ q →
  ∀ trace : TypedTrace S K C τ q t,
    ∀ r, r ∈ vertices trace → InWindow S K C τ r

end LogicLineages.PersistentMarking.NumberedWindowPreservationTargets
