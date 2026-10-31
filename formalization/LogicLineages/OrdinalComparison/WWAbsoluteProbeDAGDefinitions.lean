module
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGDefinitions
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG
open GroundEquivalence GroundClosing

/-- Only the shared free context is substituted; local binders survive. -/
def prefixMap {Γ Δ} (r : GroundMap Γ Δ) : (ps : List Ty) → GroundMap (ps++Γ) (ps++Δ)
  | [] => r
  | _::ps => GroundMap.lift (prefixMap r ps)

/-- One primitive output vertex for each input vertex, including variable-to-zero replacement. -/
def mapGraph {Γ Δ ss} (r : GroundMap Γ Δ) : DAG Γ ss → DAG Δ ss
  | .nil => .nil
  | .var (Δ:=ps) d x => match prefixMap r ps x with
    | .var y => .var (mapGraph r d) y
    | .zero => .zero (mapGraph r d)
  | .app d f a => .app (mapGraph r d) f a
  | .lam d b => .lam (mapGraph r d) b
  | .zero d => .zero (mapGraph r d)
  | .succ d => .succ (mapGraph r d)
  | .case d τ => .case (mapGraph r d) τ
  | .recursor d τ => .recursor (mapGraph r d) τ

def mapInput {Γ Δ τ} (r : GroundMap Γ Δ) (d : Input Γ τ) : Input Δ τ :=
  ⟨d.specs,mapGraph r d.graph,d.root⟩
def closeInput {Γ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (d : Input Γ τ) : Input [] τ :=
  mapInput (AbsoluteObserver.closingMap hΓ) d

/-- Two genuine applications and two genuine unused binders; no beta reduction. -/
def probeInput {Γ τ} (d : Input Γ τ) (x : Variable Γ .ground) : Input Γ .ground :=
  let l := DAG.lam (Δ:=[]) d.graph.insert (d.root.map insertSpec)
  let v := DAG.var (Δ:=[]) l x
  let a := DAG.app v (.there .here) .here
  let z := DAG.zero (Δ:=[τ]) a
  let e := DAG.lam (Δ:=[]) z .here
  ⟨_,DAG.app e .here (.there (.there .here)),.here⟩
def originalInput {Γ τ} (d : Input Γ τ) : Input (.ground::.ground::Γ) .ground :=
  probeInput (ScopedDAG.renameInput (AbsoluteObserver.shiftTwo Γ) d) .here
def closedInput {Γ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (d : Input Γ τ) : Input (.ground::.ground::Γ) .ground :=
  probeInput (ScopedDAG.renameInput (AbsoluteObserver.fromEmpty _) (closeInput hΓ d)) (.there .here)
end LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG
