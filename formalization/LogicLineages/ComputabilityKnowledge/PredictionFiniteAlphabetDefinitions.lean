module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeTableDefinitions
@[expose] public section
/-! Variable finite work alphabets. Width is at least three: 0 is blank,
1/2 are raw binary input symbols. Writes/reads are interpreted modulo width
in an actual Fin-width TM0 machine. No pre-scan of the input is charged. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabet
open Turing
abbrev Action := Bool ⊕ Nat
abbrev Table := Nat × Nat × List (Option (Nat × Action))
abbrev Raw := Nat × Nat × List Nat × List Nat

def width (p : Table) : Nat := p.1 + 3

instance (p : Table) : Inhabited (Fin (width p)) :=
  ⟨⟨0, by unfold width; omega⟩⟩

def decodeTable (code : Nat) : Table :=
  (Encodable.decode (α := Table) code).getD (0, 0, [])

def lookup (p : Table) (q a : Nat) : Option (Nat × Action) :=
  (p.2.2[q * width p + a % width p]?).bind id

def symbol (p : Table) (a : Nat) : Fin (width p) :=
  ⟨a % width p, Nat.mod_lt _ (by unfold width; omega)⟩

def actionStmt (p : Table) : Action → TM0.Stmt (Fin (width p))
  | .inl false => .move .left
  | .inl true => .move .right
  | .inr a => .write (symbol p a)

def machine (p : Table) : TM0.Machine (Fin (width p)) Nat :=
  fun q a => (lookup p q a.val).map (fun x => (x.1, actionStmt p x.2))

def execute (q : Nat) (a : Action) (c : Raw) : Raw :=
  match a with
  | .inl false => (q, c.2.2.1.headI, c.2.2.1.tail, c.2.1 :: c.2.2.2)
  | .inl true => (q, c.2.2.2.headI, c.2.1 :: c.2.2.1, c.2.2.2.tail)
  | .inr b => (q, b, c.2.2.1, c.2.2.2)

def step (p : Table) (c : Raw) : Option Raw :=
  (lookup p c.1 c.2.1).map (fun x => execute x.1 x.2 c)

def toCfg (p : Table) (c : Raw) : TM0.Cfg (Fin (width p)) Nat :=
  ⟨c.1, ⟨symbol p c.2.1, ListBlank.mk (c.2.2.1.map (symbol p)),
    ListBlank.mk (c.2.2.2.map (symbol p))⟩⟩

def inputSymbol (b : Bool) : Nat := if b then 2 else 1

def initial (p : Table) (xs : List Bool) : Raw :=
  (p.2.1, (xs.map inputSymbol).headI, [], (xs.map inputSymbol).tail)

def bounded (p : Table) : Nat → Raw → Option Raw
  | 0, _ => none
  | n + 1, c => match step p c with
    | none => some c
    | some c' => bounded p n c'

inductive Run (p : Table) : Raw → Raw → Nat → Prop
  | refl (c : Raw) : Run p c c 0
  | next {c c' d : Raw} {n : Nat} :
      step p c = some c' → Run p c' d n → Run p c d (n + 1)

def simulate (code fuel : Nat) (xs : List Bool) : Option Raw :=
  bounded (decodeTable code) fuel (initial (decodeTable code) xs)

end LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabet
