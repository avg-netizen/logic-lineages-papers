module
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode.Targets
open SyntaxCode

def RawExact : Prop := ∀ fresh depth t, mapCode fresh depth (code t) = code (mapRaw fresh depth t)

def TypedExact : Prop := ∀ (Γ Δ : List Ty) (τ : Ty) (fresh : Bool) (depth : Nat)
    (r : GroundClosing.GroundMap Γ Δ), Compatible fresh depth r → ∀ (t : OriginalTerm Γ τ),
  mapCode fresh depth (encodeTerm t) = encodeTerm (t.substitute r.source)

/-- Actual source maps, with no supplied compatibility hypothesis; the
arbitrary-depth typed theorem pays capture avoidance inside all internal binders. -/
def ConcreteExact : Prop :=
  (∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm (.ground :: Γ) τ),
    mapCode false 0 (encodeTerm t) = encodeTerm (GroundOperatorDischarge.close t)) ∧
  (∀ (Γ : List Ty) (σ τ : Ty) (t : OriginalTerm (σ :: Γ) τ),
    mapCode true 0 (encodeTerm t) = encodeTerm (t.rename UnaryCarrier.renameTracked))

def PrimitiveRecursive : Prop := Primrec (fun p : Bool × Nat × Nat => mapCode p.1 p.2.1 p.2.2)
end LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode.Targets
