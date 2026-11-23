module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSyntax

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOrdinaryTranslation
open NumberedWindowSyntax

/- The manuscript's ordinary tr. It follows the literal original
constructors, so original application heads remain ordinary heads.
The paper does not define tr for a symbolic marked term. -/
mutual
def tr : Spine.Expr → Option NTerm
  | .free σ x => some (.free σ x)
  | .bound σ i => some (.bound σ i)
  | .lam σ q => (tr q).map (.lam σ)
  | .head f bs => (trArgs bs).map (.ordinary f)
  | .marked _ _ _ _ => none
def trArgs : Spine.Args → Option NArgs
  | .nil => some .nil
  | .cons q qs => do
    let r ← tr q
    let rs ← trArgs qs
    pure (.cons r rs)
end

end LogicLineages.PersistentMarking.NumberedWindowOrdinaryTranslation
