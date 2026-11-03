module
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationTreeCode

def leafCode (payload : Nat) : Nat := 4*payload
def freeCode (metadata child : Nat) : Nat := 4*Nat.pair metadata child+1
def activeCode (metadata left right : Nat) : Nat := 4*Nat.pair metadata (Nat.pair left right)+2

def freeMetadata (left right : List Ty) (σ : Ty) (d : Nat) : Nat :=
  Encodable.encode (left.map SyntaxCode.typeCode,right.map SyntaxCode.typeCode,SyntaxCode.typeCode σ,d)
def activeMetadata (left right : List Ty) (σ : Ty) (p d d' c : Nat) : Nat :=
  Encodable.encode (left.map SyntaxCode.typeCode,right.map SyntaxCode.typeCode,SyntaxCode.typeCode σ,p,d,d',c)

/-- All source payloads, context/type fields and coefficients remain literal.
Children retain their order and repeated occurrences. Proof fields erase only. -/
def code {α : Type} [Encodable α] {Γ : List Ty} : UnitElimination.Tree α Γ → Nat
  | .leaf b => leafCode (Encodable.encode (UnitGroundBlockCode.blockCode b))
  | .free left right σ d q => freeCode (freeMetadata left right σ d) (code q)
  | .active left right σ p d d' c q r => activeCode (activeMetadata left right σ p d d' c) (code q) (code r)

def fold (leaf : Nat → Nat) (free : Nat → Nat → Nat) (active : Nat → Nat → Nat → Nat) : Nat → Nat
  | n =>
    if h : n%4=1 ∨ n%4=2 then
      have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/4).unpair
      have hc : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%4=1 then free p.1 (fold leaf free active p.2)
      else
        have hl : p.2.unpair.1<n := (Nat.unpair_left_le _).trans_lt hc
        have hr : p.2.unpair.2<n := (Nat.unpair_right_le _).trans_lt hc
        active p.1 (fold leaf free active p.2.unpair.1) (fold leaf free active p.2.unpair.2)
    else leaf (n/4)
termination_by n => n
decreasing_by all_goals assumption

def treeFold {α : Type} [Encodable α] (leaf : Nat → Nat) (free : Nat → Nat → Nat)
    (active : Nat → Nat → Nat → Nat) {Γ : List Ty} : UnitElimination.Tree α Γ → Nat
  | .leaf b => leaf (Encodable.encode (UnitGroundBlockCode.blockCode b))
  | .free left right σ d q => free (freeMetadata left right σ d) (treeFold leaf free active q)
  | .active left right σ p d d' c q r => active (activeMetadata left right σ p d d' c)
      (treeFold leaf free active q) (treeFold leaf free active r)

noncomputable def realizeLeaf (n : Nat) : Nat := leafCode (Encodable.encode
  (UnitGroundBlockCode.realizeCode ((Encodable.decode (α := UnitGroundBlockCode.Payload (Nat×Nat)) n).getD
    (0,0,0,0,(0,0)))))
noncomputable def realizeCode (n : Nat) : Nat := fold realizeLeaf freeCode activeCode n
end LogicLineages.OrdinalComparison.Source.UnitEliminationTreeCode
