import LogicLineages.PersistentMarking.NumberedWindowClosing

namespace LogicLineages.PersistentMarking.NumberedWindowTraceAlgebra
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowPrimary
open NumberedWindowPreservationTargets

/-- Exactly the sources of the stored edges. The last vertex is included
by `vertices`, not repeated here when two traces are concatenated. -/
def termSources {S K C τ} {q r : NTerm} : TypedTrace S K C τ q r → List NTerm
  | .done _ => []
  | .raw _ _ _ tail => q :: termSources tail
  | .equiv _ tail => q :: termSources tail

/-- The actual number of raw edges is separate from primary equivalence
witnesses. This predicate excludes every equivalence member of the trace. -/
def onlyRaw {S K C τ} {q r : NTerm} : TypedTrace S K C τ q r → Prop
  | .done _ => True
  | .raw _ _ _ tail => onlyRaw tail
  | .equiv _ _ => False

/-- Literal ordered-base context traces. No tuple-wide raw step is added:
the existing RawArgsStep replaces one actual position. Primary steps
use the existing typed ordered congruence, not an arbitrary permutation. -/
inductive ArgsTrace (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (types : List Ty) : NArgs → NArgs → Type where
  | done : BaseTyped C qs types → ArgsTrace S K C types qs qs
  | raw : BaseTyped C qs types → BaseTyped C rs types → RawArgsStep S K qs rs →
      ArgsTrace S K C types rs ts → ArgsTrace S K C types qs ts
  | equiv : OrderedPrimary S K C types qs rs →
      ArgsTrace S K C types rs ts → ArgsTrace S K C types qs ts

def argsVertices {S K C types} {qs rs : NArgs} : ArgsTrace S K C types qs rs → List NArgs
  | .done _ => [qs]
  | .raw _ _ _ tail => qs :: argsVertices tail
  | .equiv _ tail => qs :: argsVertices tail

def argsSources {S K C types} {qs rs : NArgs} : ArgsTrace S K C types qs rs → List NArgs
  | .done _ => []
  | .raw _ _ _ tail => qs :: argsSources tail
  | .equiv _ tail => qs :: argsSources tail

def argsRawLength {S K C types} {qs rs : NArgs} : ArgsTrace S K C types qs rs → Nat
  | .done _ => 0
  | .raw _ _ _ tail => argsRawLength tail + 1
  | .equiv _ tail => argsRawLength tail

end LogicLineages.PersistentMarking.NumberedWindowTraceAlgebra
