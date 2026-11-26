import LogicLineages.PersistentMarking.StructuralContext
import LogicLineages.PersistentMarking.Comparison
namespace LogicLineages.PersistentMarking.StructuralStabilityTargets
open Spine NameBridge StructuralContext

def OrdinaryMap (S : Signature) (θ : FreeMap) : Prop :=
  ∀ σ x, PaperTerm S (θ σ x) σ ∧ Ordinary (θ σ x)

def CloseTyped : Prop := ∀ name q τ, Typed EmptyContext q τ →
  Typed (EmptyContext.push name.1) (close name q) τ

def CloseValidity : Prop := ∀ S name q, Valid S q → Valid S (close name q)
def CloseOrdinary : Prop := ∀ name q, Ordinary q → Ordinary (close name q)
def CloseAbsence : Prop := ∀ name other q,
  freeOccurs other q = false → freeOccurs other (close name q) = false

def CloseOpen : Prop := ∀ name y q τ, Typed EmptyContext q τ →
  openBody name.1 y (close name q) = freeSub (openingMap name y) 0 q

def NamedClosing : Prop := ∀ name q,
  encode [name] q = close name (encode [] q)

def NamedFill : Prop := ∀ C q,
  encode [] (namedFill C q) = fill (encodeContext C) (encode [] q)

def FillPaper : Prop := ∀ S C σ τ q, ContextTyped S C σ τ →
  PaperTerm S q σ → PaperTerm S (fill C q) τ

def FillOrdinary : Prop := ∀ S C σ τ q, ContextTyped S C σ τ →
  Ordinary q → Ordinary (fill C q)

def WeakSubstitution : Prop := ∀ S s t θ,
  Ordinary s → Ordinary t → OrdinaryMap S θ → Weak S s t →
  Weak S (freeSub θ 0 s) (freeSub θ 0 t)

def StrictSubstitution : Prop := ∀ S s t θ,
  Ordinary s → Ordinary t → OrdinaryMap S θ → Strict S s t →
  Strict S (freeSub θ 0 s) (freeSub θ 0 t)

def WeakContext : Prop := ∀ S C σ τ s t, ContextTyped S C σ τ →
  PaperTerm S s σ → PaperTerm S t σ → Ordinary s → Ordinary t → Weak S s t →
  Weak S (fill C s) (fill C t)

def StrictContext : Prop := ∀ S C σ τ s t, ContextTyped S C σ τ →
  PaperTerm S s σ → PaperTerm S t σ → Ordinary s → Ordinary t → Strict S s t →
  Strict S (fill C s) (fill C t)

def FullStability : Prop := WeakSubstitution ∧ StrictSubstitution ∧ WeakContext ∧ StrictContext
end LogicLineages.PersistentMarking.StructuralStabilityTargets
