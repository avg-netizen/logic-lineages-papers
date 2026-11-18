module
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence
abbrev Node := List Nat × (Nat × (Nat × List Nat))
abbrev Code := List Nat × (List Node × (Nat × Nat))
abbrev Packed := Σ Γ : List Ty, Σ τ : Ty, Input Γ τ
abbrev Graph (Γ : List Ty) := Σ ss : List Spec, DAG Γ ss

def variableIndex {Γ τ} : Variable Γ τ → Nat
  | .here => 0
  | .there x => variableIndex x + 1
def referenceIndex {ss s} : Ref ss s → Nat
  | .here => 0
  | .there r => referenceIndex r + 1
def getVariable : (Γ : List Ty) → (τ : Ty) → Nat → Option (Variable Γ τ)
  | [], _, _ => none
  | σ::Γ, τ, 0 => if h : σ = τ then some (by cases h; exact Variable.here) else none
  | _::Γ, τ, n+1 => (getVariable Γ τ n).map Variable.there
def getReference : (ss : List Spec) → (s : Spec) → Nat → Option (Ref ss s)
  | [], _, _ => none
  | t::ss, s, 0 => if h : t = s then some (by cases h; exact Ref.here) else none
  | _::ss, s, n+1 => (getReference ss s n).map Ref.there

def node (Δ : List Ty) (τ : Ty) (tag : Nat) (args : List Nat) : Node :=
  (Δ.map SyntaxCode.typeCode,SyntaxCode.typeCode τ,tag,args)
def encodeGraph {Γ ss} : DAG Γ ss → List Node
  | .nil => []
  | .var (Δ:=Δ) (τ:=τ) d x => node Δ τ 0 [variableIndex x] :: encodeGraph d
  | .app (Δ:=Δ) (σ:=σ) (τ:=τ) d f a =>
      node Δ τ 1 [SyntaxCode.typeCode σ,referenceIndex f,referenceIndex a] :: encodeGraph d
  | .lam (Δ:=Δ) (σ:=σ) (τ:=τ) d b =>
      node Δ (.arrow σ τ) 2 [SyntaxCode.typeCode σ,SyntaxCode.typeCode τ,referenceIndex b] :: encodeGraph d
  | .zero (Δ:=Δ) d => node Δ .ground 3 [] :: encodeGraph d
  | .succ (Δ:=Δ) d => node Δ (.arrow .ground .ground) 4 [] :: encodeGraph d
  | .case (Δ:=Δ) d τ => node Δ τ.caseType 5 [SyntaxCode.typeCode τ] :: encodeGraph d
  | .recursor (Δ:=Δ) d τ => node Δ τ.recType 6 [SyntaxCode.typeCode τ] :: encodeGraph d

def step (Γ : List Ty) (a : Node) (g : Graph Γ) : Option (Graph Γ) := do
  let Δ := a.1.map SyntaxCode.decodeType
  let τ := SyntaxCode.decodeType a.2.1
  let ⟨ss,d⟩ := g
  match a.2.2.1, a.2.2.2 with
  | 0,[i] =>
      let x ← getVariable (Δ++Γ) τ i
      return ⟨_,DAG.var d x⟩
  | 1,[s,i,j] =>
      let σ := SyntaxCode.decodeType s
      let f ← getReference ss (Δ,.arrow σ τ) i
      let x ← getReference ss (Δ,σ) j
      return ⟨_,DAG.app d f x⟩
  | 2,[s,t,i] =>
      let σ := SyntaxCode.decodeType s
      let υ := SyntaxCode.decodeType t
      if τ = .arrow σ υ then
        let b ← getReference ss (σ::Δ,υ) i
        return ⟨_,DAG.lam d b⟩
      else none
  | 3,[] => if τ = .ground then return ⟨_,DAG.zero (Δ:=Δ) d⟩ else none
  | 4,[] => if τ = .arrow .ground .ground then return ⟨_,DAG.succ (Δ:=Δ) d⟩ else none
  | 5,[t] =>
      let υ := SyntaxCode.decodeType t
      if τ = υ.caseType then return ⟨_,DAG.case (Δ:=Δ) d υ⟩ else none
  | 6,[t] =>
      let υ := SyntaxCode.decodeType t
      if τ = υ.recType then return ⟨_,DAG.recursor (Δ:=Δ) d υ⟩ else none
  | _,_ => none

def decodeGraph (Γ : List Ty) : List Node → Option (Graph Γ)
  | [] => some ⟨[],DAG.nil⟩
  | a::as => (decodeGraph Γ as).bind (step Γ a)
def encode (d : Packed) : Code :=
  (d.1.map SyntaxCode.typeCode,encodeGraph d.2.2.graph,referenceIndex d.2.2.root,SyntaxCode.typeCode d.2.1)
def decode (c : Code) : Option Packed := do
  let Γ := c.1.map SyntaxCode.decodeType
  let τ := SyntaxCode.decodeType c.2.2.2
  let ⟨ss,g⟩ ← decodeGraph Γ c.2.1
  let r ← getReference ss ([],τ) c.2.2.1
  return ⟨Γ,τ,⟨ss,g,r⟩⟩
/-- Total effective reification on raw data; rejected inputs yield none. -/
def reifyCode (c : Code) : Option Code := (decode c).map encode
def valid (c : Code) : Bool := (decode c).isSome
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG
