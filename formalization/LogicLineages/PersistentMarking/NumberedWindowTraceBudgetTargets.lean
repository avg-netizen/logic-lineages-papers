import LogicLineages.PersistentMarking.NumberedWindowTraceAlgebra
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryTranslation
import LogicLineages.PersistentMarking.NumberedWindowTupleTargets
import LogicLineages.PersistentMarking.SpineMarking

namespace LogicLineages.PersistentMarking.NumberedWindowTraceBudgetTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowPrimary
open NumberedWindowPreservationTargets NumberedWindowClosing NumberedWindowTraceAlgebra
open NumberedWindowOrdinaryTranslation NumberedWindowTupleTargets

def LiteralTermVertices : Prop := ∀ S K C τ q r (trace : TypedTrace S K C τ q r),
  vertices trace = termSources trace ++ [r]

def LiteralArgsVertices : Prop := ∀ S K C ts qs rs (trace : ArgsTrace S K C ts qs rs),
  argsVertices trace = argsSources trace ++ [rs]

def JoinTermTraces : Prop := ∀ S K C τ q r t
    (left : TypedTrace S K C τ q r) (right : TypedTrace S K C τ r t),
  ∃ out : TypedTrace S K C τ q t,
    vertices out = termSources left ++ vertices right ∧
    rawLength out = rawLength left + rawLength right

def JoinArgsTraces : Prop := ∀ S K C types qs rs ts
    (left : ArgsTrace S K C types qs rs) (right : ArgsTrace S K C types rs ts),
  ∃ out : ArgsTrace S K C types qs ts,
    argsVertices out = argsSources left ++ argsVertices right ∧
    argsRawLength out = argsRawLength left + argsRawLength right

def LiftTypedLambda : Prop := ∀ S K (C : Spine.BoundContext) σ τ q r
    (trace : TypedTrace S K (C.push σ) τ q r),
  ∃ out : TypedTrace S K C (.arrow σ τ) (.lam σ q) (.lam σ r),
    vertices out = (vertices trace).map (.lam σ) ∧ rawLength out = rawLength trace

def LiftTypedAuxFunction : Prop := ∀ S K C σ τ a q r,
  Typed C a σ → ∀ trace : TypedTrace S K C (.arrow σ τ) q r,
    ∃ out : TypedTrace S K C τ (.auxApp σ τ q a) (.auxApp σ τ r a),
      vertices out = (vertices trace).map (fun p => .auxApp σ τ p a) ∧
      rawLength out = rawLength trace

def WindowPathAsRawTrace : Prop := ∀ S K C τ q r,
  WindowPath S K C τ q r → ∃ trace : TypedTrace S K C τ q r, onlyRaw trace

/-- First perform actual changes in the first argument, then the actual
tail changes. Every recorded vertex is the literal cons image and the
join's common vertex appears once. -/
def ConsTypedTrace : Prop := ∀ S K C σ types q r qs rs
    (first : TypedTrace S K C σ q r) (tail : ArgsTrace S K C types qs rs),
  ∃ out : ArgsTrace S K C (σ::types) (.cons q qs) (.cons r rs),
    argsVertices out = (termSources first).map (fun t => .cons t qs) ++
      (argsVertices tail).map (.cons r) ∧
    argsRawLength out = rawLength first + argsRawLength tail

def LiftTypedOrdinaryBase : Prop := ∀ S K C (f : Head) bs cs
    (trace : ArgsTrace S K C f.arguments bs cs),
  ∃ out : TypedTrace S K C f.result (.ordinary f bs) (.ordinary f cs),
    vertices out = (argsVertices trace).map (.ordinary f) ∧
    rawLength out = argsRawLength trace

def OrdinaryTrDomain : Prop := ∀ q, (∃ Q, tr q = some Q) ↔ Spine.Ordinary q

def OrdinaryTrArgsDomain : Prop := ∀ qs, (∃ As, trArgs qs = some As) ↔ Spine.OrdinaryArgs qs

def UniqueOrdinaryRealization : Prop := ∀ q Q, tr q = some Q →
  ∀ n, Realizes n q Q ∧ ∀ R, Realizes n q R → R = Q

def UniqueOrdinaryArgsRealization : Prop := ∀ qs As, trArgs qs = some As →
  ∀ n, RealizesArgs n qs As ∧ ∀ Bs, RealizesArgs n qs Bs → Bs = As

/-- The actual source partial mark, not mark of an arbitrary term. Even
if the symbolic mark is already identical, the numerical label genuinely
decreases. At threshold n+1 one *actual* raw step and one primitive mark
decrease both lead to a realization at n, in the same typed head window. -/
def OneReservedMarkStep : Prop := ∀ S K C τ n (q r : Spine.Expr) (Q : NTerm),
  DecisionSourceUniverse.Closed K →
  Spine.mark q = some r → Realizes (n+1) q Q → InWindow S K C τ Q →
  ∃ R, MarkDecrease Q R ∧ RawStep S K Q R ∧ InWindow S K C τ R ∧ Realizes n r R

end LogicLineages.PersistentMarking.NumberedWindowTraceBudgetTargets
