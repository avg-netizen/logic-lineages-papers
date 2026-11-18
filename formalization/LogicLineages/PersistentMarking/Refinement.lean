import LogicLineages.PersistentMarking.AuxiliaryWitnesses
namespace LogicLineages.PersistentMarking.Spine
open NameBridge (openBody freeOccurs)

/- Explicit finite data trees; logical refinement is existence of a tree.
The whole-owner extra witness below is a genuine smaller premise tree. -/
mutual
 inductive RefinementTree (S : Signature) : Expr → Expr → Type where
   | var : RefinementTree S (.free σ x) (.free σ x)
   | abs : PaperTerm S (.lam σ q) (.arrow σ τ) → PaperTerm S (.lam σ s) (.arrow σ τ) →
       freeOccurs (σ,x) q = false → freeOccurs (σ,x) s = false →
       RefinementTree S (openBody σ x q) (openBody σ x s) →
       RefinementTree S (.lam σ q) (.lam σ s)
   | head : PaperTerm S (.head f qs) f.result → PaperTerm S (.head f ss) f.result →
       RefinementBasesTree S qs ss → RefinementTree S (.head f qs) (.head f ss)
   | marked : PaperTerm S (.marked f τ qb qe) τ → PaperTerm S (.marked f τ sb se) τ →
       RefinementBasesTree S qb sb → RefinementExtrasTree S f qb qe se →
       RefinementTree S (.marked f τ qb qe) (.marked f τ sb se)
 inductive RefinementBasesTree (S : Signature) : Args → Args → Type where
   | nil : RefinementBasesTree S .nil .nil
   | cons : RefinementTree S q s → RefinementBasesTree S qs ss →
       RefinementBasesTree S (.cons q qs) (.cons s ss)
 inductive RefinementExtraTree (S : Signature) : Head → Args → Args → Expr → Type where
   | existing : At extras i q → RefinementTree S q s → RefinementExtraTree S f base extras s
   | owner : RefinementTree S (.marked f s.type base extras) s → RefinementExtraTree S f base extras s
 inductive RefinementExtrasTree (S : Signature) : Head → Args → Args → Args → Type where
   | nil : RefinementExtrasTree S f base extras .nil
   | cons : RefinementExtraTree S f base extras q → RefinementExtrasTree S f base extras qs →
       RefinementExtrasTree S f base extras (.cons q qs)
end

def Refines (S : Signature) (q s : Expr) : Prop := _root_.Nonempty (RefinementTree S q s)

end LogicLineages.PersistentMarking.Spine
