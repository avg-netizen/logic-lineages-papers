module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodecProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodec
open Turing.PartrecToTM2 PredictionCompilerFinitePayloadCodec
abbrev Label := Λ'

/-- Use the chosen primitive coding explicitly, never a competing bare Encodable instance. -/
def putNat {α : Type} [i : Primcodable α] (x : α) : Nat := @Encodable.encode α i.toEncodable x

def pack (t : Quint Nat) : Nat := Nat.pair t.1 (Nat.pair t.2.1 (Nat.pair t.2.2.1 (Nat.pair t.2.2.2.1 t.2.2.2.2)))
def unpack (n : Nat) : Quint Nat :=
  (n.unpair.1, n.unpair.2.unpair.1, n.unpair.2.unpair.2.unpair.1,
    n.unpair.2.unpair.2.unpair.2.unpair.1, n.unpair.2.unpair.2.unpair.2.unpair.2)
def node (tag payload : Nat) (cs : Quint Nat) : Nat := 8 * Nat.pair payload (pack cs) + tag + 1

def code : Label → Nat
  | .move p k₁ k₂ q => node 0 (putNat (p, k₁, k₂)) (code q, 0, 0, 0, 0)
  | .clear p k q => node 1 (putNat (p, k)) (code q, 0, 0, 0, 0)
  | .copy q => node 2 0 (code q, 0, 0, 0, 0)
  | .push k s q => node 3 (putNat (k, s)) (code q, 0, 0, 0, 0)
  | .read f => node 4 0 (code (f none), code (f (some .consₗ)), code (f (some .cons)),
      code (f (some .bit0)), code (f (some .bit1)))
  | .succ q => node 5 0 (code q, 0, 0, 0, 0)
  | .pred q₁ q₂ => node 6 0 (code q₁, code q₂, 0, 0, 0)
  | .ret k => node 7 (putNat k) (0, 0, 0, 0, 0)

/-- Fixed-five-branch numerical fold. Zero is a total malformed-word fallback.
Every recursive child is strictly smaller than its positive parent word. -/
def fold {α : Type} (z : α) (step : Nat → Nat → Quint α → α) : Nat → α
  | n => if h : n = 0 then z else
    let m := (n - 1) / 8
    let r := m.unpair.2
    have hm : m < n := (Nat.div_le_self _ _).trans_lt (by omega)
    have hr : r < n := (Nat.unpair_right_le _).trans_lt hm
    have hr₂ : r.unpair.2 < n := (Nat.unpair_right_le _).trans_lt hr
    have hr₃ : r.unpair.2.unpair.2 < n := (Nat.unpair_right_le _).trans_lt hr₂
    have hr₄ : r.unpair.2.unpair.2.unpair.2 < n := (Nat.unpair_right_le _).trans_lt hr₃
    step ((n - 1) % 8) m.unpair.1
      (fold z step r.unpair.1, fold z step r.unpair.2.unpair.1,
        fold z step r.unpair.2.unpair.2.unpair.1,
        fold z step r.unpair.2.unpair.2.unpair.2.unpair.1,
        fold z step r.unpair.2.unpair.2.unpair.2.unpair.2)
termination_by n => n
decreasing_by
  · exact (Nat.unpair_left_le _).trans_lt hr
  · exact (Nat.unpair_left_le _).trans_lt hr₂
  · exact (Nat.unpair_left_le _).trans_lt hr₃
  · exact (Nat.unpair_left_le _).trans_lt hr₄
  · exact (Nat.unpair_right_le _).trans_lt hr₄

def termFold {α : Type} (z : α) (step : Nat → Nat → Quint α → α) : Label → α
  | .move p k₁ k₂ q => step 0 (putNat (p, k₁, k₂)) (termFold z step q, z, z, z, z)
  | .clear p k q => step 1 (putNat (p, k)) (termFold z step q, z, z, z, z)
  | .copy q => step 2 0 (termFold z step q, z, z, z, z)
  | .push k s q => step 3 (putNat (k, s)) (termFold z step q, z, z, z, z)
  | .read f => step 4 0 (termFold z step (f none), termFold z step (f (some .consₗ)),
      termFold z step (f (some .cons)), termFold z step (f (some .bit0)), termFold z step (f (some .bit1)))
  | .succ q => step 5 0 (termFold z step q, z, z, z, z)
  | .pred q₁ q₂ => step 6 0 (termFold z step q₁, termFold z step q₂, z, z, z)
  | .ret k => step 7 (putNat k) (z, z, z, z, z)

def readNat (α : Type) [i : Primcodable α] [Inhabited α] (n : Nat) : α := (@Encodable.decode α i.toEncodable n).getD default

def assemble (tag p : Nat) (cs : Quint Label) : Label :=
  if tag = 0 then
    let t := readNat ((Γ' → Bool) × K' × K') p
    .move t.1 t.2.1 t.2.2 cs.1
  else if tag = 1 then
    let t := readNat ((Γ' → Bool) × K') p
    .clear t.1 t.2 cs.1
  else if tag = 2 then .copy cs.1
  else if tag = 3 then
    let t := readNat (K' × (Option Γ' → Option Γ')) p
    .push t.1 t.2 cs.1
  else if tag = 4 then .read (tableStore cs)
  else if tag = 5 then .succ cs.1
  else if tag = 6 then .pred cs.1 cs.2.1
  else .ret (readNat Cont' p)

def decode : Nat → Label := fold (.ret .halt) assemble
def normalize (n : Nat) : Nat := code (decode n)
end LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodec
