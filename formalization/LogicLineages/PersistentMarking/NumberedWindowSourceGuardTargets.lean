import LogicLineages.PersistentMarking.NumberedWindowApplicationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowSourceGuardTargets
open Spine NumberedWindowDomain

def SourceGuard (S : Signature) (K : List Ty) (C : BoundContext) (σ : Ty) (q : Expr) : Prop :=
  Spine.Typed C q σ ∧ Valid S q ∧ SymbolicAdmissible K q

def SourceValues (S : Signature) (K : List Ty) (C : BoundContext) (types : List Ty) (values : Args) : Prop :=
  Spine.BaseTyped C values types ∧ ValidArgs S values ∧ SymbolicArgsAdmissible K values

/-- The actual original simultaneous nearest-binder-first substitution,
under an arbitrary surrounding binding context. No restriction on free
names, designated input heads, or finite observation ports. -/
def ActualBlockGuard : Prop := ∀ S K C types values q σ,
  SourceGuard S K (BoundContext.prefix types C) σ q →
  SourceValues S K C types values →
  SourceGuard S K C σ (Spine.substitute values 0 q)

def ActualBaseBlockGuard : Prop := ∀ S K C types values bs bTypes,
  SourceValues S K (BoundContext.prefix types C) bTypes bs →
  SourceValues S K C types values →
  SourceValues S K C bTypes (Spine.substituteArgs values 0 bs)

def ActualExtrasBlockGuard : Prop := ∀ S K C types values es,
  Spine.ExtrasTyped (BoundContext.prefix types C) es →
  ValidArgs S es → SymbolicArgsAdmissible K es → SourceValues S K C types values →
  Spine.ExtrasTyped C (Spine.substituteArgs values 0 es) ∧
    ValidArgs S (Spine.substituteArgs values 0 es) ∧
    SymbolicArgsAdmissible K (Spine.substituteArgs values 0 es)

end LogicLineages.PersistentMarking.NumberedWindowSourceGuardTargets
