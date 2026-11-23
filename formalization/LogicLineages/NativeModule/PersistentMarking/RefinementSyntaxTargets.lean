module

public import LogicLineages.NativeModule.PersistentMarking.AuxiliaryTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementSyntaxTargets
open Spine NameBridge

def Transitive : Prop := ∀ S q s t, Refines S q s → Refines S s t → Refines S q t

def FreeSubstitution : Prop := ∀ S γ δ q s,
  FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ →
  (∀ σ x, Refines S (γ σ x) (δ σ x)) → Refines S q s →
  Refines S (freeSub γ 0 q) (freeSub δ 0 s)

def Opening : Prop := ∀ S σ q s x,
  Refines S (.lam σ q) (.lam σ s) →
  freeOccurs (σ,x) q = false → freeOccurs (σ,x) s = false →
  Refines S (openBody σ x q) (openBody σ x s)

def Renaming : Prop := ∀ S (π : Ty → Nat → Nat) q s,
  Refines S q s →
  Refines S (freeSub (fun σ x => .free σ (π σ x)) 0 q)
    (freeSub (fun σ x => .free σ (π σ x)) 0 s)

def FullApplication : Prop := ∀ S q s as bs τ r,
  Refines S q s → _root_.Nonempty (RefinementBasesTree S as bs) →
  CallTyped EmptyContext q.type as τ → CallTyped EmptyContext s.type bs τ →
  apply s bs = some r → ∃ p, apply q as = some p ∧ Refines S p r

/-- All assertions of composition.tex lem:sharp-syntax, with opening and
renaming stated explicitly and actual operations at every endpoint. -/
def FullSyntax : Prop :=
  AuxiliaryTargets.RefinementReflexive ∧ Transitive ∧ FreeSubstitution ∧
  Opening ∧ Renaming ∧ AuxiliaryTargets.RefinementRetyping ∧
  AuxiliaryTargets.RefinementMarkReflection ∧ FullApplication

end LogicLineages.PersistentMarking.RefinementSyntaxTargets
