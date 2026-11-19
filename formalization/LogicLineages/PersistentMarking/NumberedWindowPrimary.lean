import LogicLineages.PersistentMarking.NumberedWindowRules

namespace LogicLineages.PersistentMarking.NumberedWindowPrimary
open NumberedWindowSyntax NumberedWindowDomain

/- Type-preserving primary equivalence in the actual new numbered syntax.
The only root exchanges are equivalent admitted heads within K and a
permutation of the literal typed base. Current type, finite label and
old extras are fixed there. Congruence may change either application
position by equivalence, never by an extra raw reduction rule. -/
mutual
inductive Primary (S : Spine.Signature) (K : List Ty) : Spine.BoundContext → Ty → NTerm → NTerm → Prop where
  | refl : Typed C q τ → Primary S K C τ q q
  | symm : Primary S K C τ q r → Primary S K C τ r q
  | trans : Primary S K C τ q r → Primary S K C τ r t → Primary S K C τ q t
  | ordinary :
      HeadInWindow S K f → HeadInWindow S K g → Spine.Equivalent S f g → f.result = g.result →
      BaseTyped C bs f.arguments → BaseTyped C cs g.arguments →
      bs.toList.Perm cs.toList →
      Primary S K C f.result (.ordinary f bs) (.ordinary g cs)
  | numbered :
      HeadInWindow S K f → HeadInWindow S K g → Spine.Equivalent S f g →
      BaseTyped C bs f.arguments → BaseTyped C cs g.arguments → ExtrasTyped C es →
      bs.toList.Perm cs.toList →
      Primary S K C τ (.numbered f τ k bs es) (.numbered g τ k cs es)
  | lam : Primary S K (C.push σ) τ q r →
      Primary S K C (.arrow σ τ) (.lam σ q) (.lam σ r)
  | appFunction : Primary S K C (.arrow σ τ) q r → Typed C A σ →
      Primary S K C τ (.auxApp σ τ q A) (.auxApp σ τ r A)
  | appArgument : Typed C Q (.arrow σ τ) → Primary S K C σ a b →
      Primary S K C τ (.auxApp σ τ Q a) (.auxApp σ τ Q b)
  | ordinaryArguments : OrderedPrimary S K C f.arguments bs cs →
      Primary S K C f.result (.ordinary f bs) (.ordinary f cs)
  | numberedBase : OrderedPrimary S K C f.arguments bs cs → ExtrasTyped C es →
      Primary S K C τ (.numbered f τ k bs es) (.numbered f τ k cs es)
  | numberedExtras : BaseTyped C bs f.arguments → OrderedPrimary S K C types es ds →
      Primary S K C τ (.numbered f τ k bs es) (.numbered f τ k bs ds)
inductive OrderedPrimary (S : Spine.Signature) (K : List Ty) :
    Spine.BoundContext → List Ty → NArgs → NArgs → Prop where
  | nil : OrderedPrimary S K C [] .nil .nil
  | cons : Primary S K C σ q r → OrderedPrimary S K C types xs ys →
      OrderedPrimary S K C (σ::types) (.cons q xs) (.cons r ys)
end

end LogicLineages.PersistentMarking.NumberedWindowPrimary
