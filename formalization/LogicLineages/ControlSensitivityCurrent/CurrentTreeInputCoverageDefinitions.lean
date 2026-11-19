module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage

open LogicLineages.OrdinalComparison.Source GroundEquivalence RawSourceDAG

/-- One newly appended original source root followed by its argument rows
and the earlier graph. The embedding retains every earlier typed reference. -/
structure Added (Γ : List Ty) (old : List Spec) (root : Spec) where
  tail : List Spec
  graph : DAG Γ (root :: tail)
  keep : ∀ {s : Spec}, Ref old s → Ref (root :: tail) s

/-- A finite literal source tree is also a scoped source DAG. The ambient
context and result are genuine changing term indices; the equality only
transports an existing variable into the separately stored binder prefix.
App first builds the function, then the argument, then the application. -/
def buildIn {Ξ : List Ty} {τ : Ty} (t : OriginalTerm Ξ τ)
    (Γ Δ : List Ty) (h : Δ ++ Γ = Ξ) {ss : List Spec} (d : DAG Γ ss) :
    Added Γ ss (Δ,τ) :=
  match t with
  | .var x => ⟨ss,.var d (h.symm ▸ x),fun r => .there r⟩
  | .zeroC => ⟨ss,.zero d,fun r => .there r⟩
  | .succC => ⟨ss,.succ d,fun r => .there r⟩
  | .caseC α => ⟨ss,.case d α,fun r => .there r⟩
  | .recC α => ⟨ss,.recursor d α,fun r => .there r⟩
  | .app f a =>
    let fd := buildIn f Γ Δ h d
    let ad := buildIn a Γ Δ h fd.graph
    ⟨_,.app ad.graph (ad.keep .here) .here,fun r => .there (ad.keep (fd.keep r))⟩
  | @Term.lam _ _ _ α _ b =>
    let bd := buildIn b Γ (α :: Δ) (congrArg (List.cons α) h) d
    ⟨_,.lam bd.graph .here,fun r => .there (bd.keep r)⟩
  | .ranked s _ => nomatch s
termination_by structural t

/-- Build a source DAG at its exact source context, without changing any
lexical scope or reference. -/
def build {Γ Δ : List Ty} {τ : Ty} (t : OriginalTerm (Δ ++ Γ) τ)
    {ss : List Spec} (d : DAG Γ ss) : Added Γ ss (Δ,τ) :=
  buildIn t Γ Δ rfl d

def input {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ) : Input Γ τ :=
  let r := build (Δ := []) t .nil
  ⟨_,r.graph,.here⟩

/-- Literal finite postorder row constructor for the unchanged radix-eight
source tree coding. Binder prefixes carry the same types; keeping the
independently constructed right rows in front of the left rows means the
left reference is shifted exactly by the number of right rows. -/
def rows (Γ Δ : List Nat) (code : Nat) : List Node :=
  let tag := code % 8
  let payload := code / 8
  let τ := (SyntaxCode.check (Δ ++ Γ) code).getD 0
  if tag = 0 then [(Δ,τ,0,[payload])]
  else if tag = 1 then [(Δ,τ,3,[])]
  else if tag = 2 then [(Δ,τ,4,[])]
  else if tag = 3 then [(Δ,τ,5,[payload])]
  else if tag = 4 then [(Δ,τ,6,[payload])]
  else if tag = 5 then
    let f := rows Γ Δ payload.unpair.1
    let a := rows Γ Δ payload.unpair.2
    let σ := (SyntaxCode.check (Δ ++ Γ) payload.unpair.2).getD 0
    (Δ,τ,1,[σ,a.length,0]) :: (a ++ f)
  else if tag = 6 then
    let b := rows Γ (payload.unpair.1 :: Δ) payload.unpair.2
    let β := (SyntaxCode.check ((payload.unpair.1 :: Δ) ++ Γ) payload.unpair.2).getD 0
    (Δ,τ,2,[payload.unpair.1,β,0]) :: b
  else []
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by
      try dsimp at *
      omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 8)
    have hl := Nat.unpair_left_le (code / 8)
    have hr := Nat.unpair_right_le (code / 8)
    try dsimp at *
    omega

/-- Reject ill-typed/malformed original tree codes with their existing
literal checker. No effectivity or semantic oracle is a runtime argument. -/
def compile (Γ : List Nat) (code : Nat) : Option Code :=
  (SyntaxCode.check Γ code).map fun τ => (Γ,rows Γ [] code,0,τ)

end LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage
