import LogicLineages.PersistentMarking.CutOwnerSyntax
namespace LogicLineages.PersistentMarking.CutOwnerTargets
open Spine

def Retyped : Prop := ∀ S f sb se g tb te τ,
  CutOwnerSyntax.Root S f sb se g tb te →
  PaperTerm S (.marked f τ sb se) τ → PaperTerm S (.marked g τ tb te) τ →
  ExtendedWeak S (.marked f τ sb se) (.marked g τ tb te)

def WholePrefix : Prop := ∀ S f sb se g tb te ρ σ q,
  CutOwnerSyntax.Root S f sb se g tb te →
  PaperTerm S (.marked f ρ sb se) ρ → PaperTerm S (.marked g ρ tb te) ρ →
  PrefixCopy g tb te σ q → ExtendedWeak S (.marked f σ sb se) q

def Selected : Prop := ∀ S f sb se g tb te q i,
  CutOwnerSyntax.Root S f sb se g tb te → (At tb i q ∨ At te i q) →
  (∃ p j, (At sb j p ∨ At se j p) ∧ ExtendedWeak S p q) ∨
    ExtendedWeak S (.marked f q.type sb se) q

def FullOwnerSuppliers : Prop := Retyped ∧ WholePrefix ∧ Selected
end LogicLineages.PersistentMarking.CutOwnerTargets
