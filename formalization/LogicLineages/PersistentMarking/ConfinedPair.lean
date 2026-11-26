import LogicLineages.PersistentMarking.TypeSupportTargets
namespace LogicLineages.PersistentMarking.ConfinedPair
open Spine TypeSupport

def Domain (S : Signature) (s t : Expr) : Prop :=
  ∃ τ, PaperTerm S s τ ∧ PaperTerm S t τ ∧ Ordinary s ∧ Ordinary t

def Weak (S : Signature) (s t : Expr) : Prop :=
  Domain S s t ∧ Spine.Weak S s t ∧ Included t s

def Strict (S : Signature) (s t : Expr) : Prop :=
  Domain S s t ∧ Spine.Strict S s t ∧ Included t s
end LogicLineages.PersistentMarking.ConfinedPair
