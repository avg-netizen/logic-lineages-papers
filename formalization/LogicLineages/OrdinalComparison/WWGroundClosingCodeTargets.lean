module
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundClosingCode.Targets
open SyntaxCode

def PrimitiveRecursive : Prop := Primrec₂ closeCode

def RawExact : Prop := ∀ (depth : Nat) (t : Raw), closeCode depth (code t) = code (closeRaw depth t)

def TypedExact : Prop := ∀ (Γ Δ : List Ty) (τ : Ty) (depth : Nat)
  (r : GroundClosing.GroundMap Γ Δ), Compatible depth r → ∀ (t : OriginalTerm Γ τ),
  closeCode depth (encodeTerm t) = encodeTerm (t.substitute r.source)

def ClosedExact : Prop := ∀ (Γ : List Ty) (τ : Ty)
  (r : GroundClosing.GroundMap Γ []) (t : OriginalTerm Γ τ),
  closeCode 0 (encodeTerm t) = encodeTerm (t.substitute r.source)
end LogicLineages.OrdinalComparison.Source.GroundClosingCode.Targets
