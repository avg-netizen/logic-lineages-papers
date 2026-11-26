import LogicLineages.PersistentMarking.NumberedWindowPositiveSimulationTargets
import LogicLineages.PersistentMarking.LiteralDerivationLocalityTargets

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationJobs
open LiteralDerivationTree LiteralDerivationLocalityTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowOrdinaryTranslation NumberedWindowSimulationData
open NumberedWindowTraceAlgebra NumberedWindowPositiveSimulationTargets

abbrev E : Spine.BoundContext := Spine.EmptyContext

def Foot (K : List Ty) {S : Spine.Signature} {J : Judgment} (d : Tree S J) : Prop :=
  ∀ ρ, ρ ∈ footprint d → ρ ∈ K

def types : Spine.Args → List Ty
  | .nil => []
  | .cons q qs => q.type :: types qs

/-- Internal strengthened strict job exposes the original first mark
separately. Stat Coverage uses this vertex and then its weak continuation. -/
def PreparedStrict (S : Spine.Signature) (K : List Ty) (τ : Ty) (Q : NTerm) (t : Spine.Expr) : Prop :=
  ∃ R, MarkDecrease Q R ∧ RawStep S K Q R ∧ InWindow S K E τ Q ∧
    InWindow S K E τ R ∧ WeakResult S K τ R t

/-- Exact target order is retained. Only the realized source base, before
the trace, is reordered by a permitted occurrence permutation. -/
def Matched (S : Spine.Signature) (K : List Ty) (Qs : NArgs) (ts : Spine.Args) : Prop :=
  ∃ start out, Qs.toList.Perm start.toList ∧ trArgs ts = some out ∧
    Nonempty (ArgsTrace S K E (types ts) start out)

def Covered (S : Spine.Signature) (K : List Ty) (removed : NArgs) (ts : Spine.Args) : Prop :=
  ∃ start out, trArgs ts = some out ∧
    (∀ a ∈ start.toList, ∃ b ∈ removed.toList, MarkDecrease b a) ∧
    Nonempty (ArgsTrace S K E (types ts) start out)

def Replaced (S : Spine.Signature) (K : List Ty) (old : NArgs) (ts : Spine.Args) : Prop :=
  ∃ start out, trArgs ts = some out ∧ PrimitiveReplacement old start ∧
    Nonempty (ArgsTrace S K E (types ts) start out)

def WholeResult (S : Spine.Signature) (K : List Ty) (f : Head) (k : Nat)
    (bs es : NArgs) (ts : Spine.Args) : Prop :=
  ∃ out, trArgs ts = some out ∧
    Nonempty (ArgsTrace S K E (types ts) (ownerCopies f k bs es (types ts)) out)

/-- One motive for the literal six sorts. The proof of the full endpoint
will discharge Foot using exact same-certificate symbolic locality. -/
def Job (S : Spine.Signature) (K : List Ty) {J : Judgment} (d : Tree S J) : Prop :=
  Foot K d → match J with
  | .weak q t =>
    ∀ n Q, budget d ≤ n → Realizes n q Q → WeakResult S K q.type Q t
  | .strict q t =>
    ∀ n Q, budget d ≤ n → Realizes n q Q → PreparedStrict S K q.type Q t
  | .matching qs ts =>
    ∀ n Qs, budget d ≤ n → RealizesArgs n qs Qs → Matched S K Qs ts
  | .multiset qs ts =>
    ∀ n Qs, budget d ≤ n → RealizesArgs n qs Qs → Replaced S K Qs ts
  | .coverage qs ts =>
    ∀ n Qs, budget d ≤ n → RealizesArgs n qs Qs → Covered S K Qs ts
  | .whole f bs es ts =>
    ∀ n k Bs Es, budget d ≤ n → n ≤ k → RealizesArgs n bs Bs → RealizesArgs n es Es →
      WholeResult S K f k Bs Es ts

end LogicLineages.PersistentMarking.NumberedWindowSimulationJobs
