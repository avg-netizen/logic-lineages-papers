module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecProof

@[expose] public section
/-! Literal numeric weakening for the actual auxiliary syntax. The cutoff counts
protected binders, so lambda descent increments it. Every constructor, head,
numbered label, output type and base/extra argument order is retained. This is
a computational supplier for root certificates, not a new reduction rule.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShift
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction

def shiftVariable (cutoff index : Nat) : Nat := if index<cutoff then index else index+1

def shiftCode {Symbol : Type} (cutoff : Nat) : Code Symbol → Code Symbol
  | .var index => .var (shiftVariable cutoff index)
  | .lam sigma body => .lam sigma (shiftCode (cutoff+1) body)
  | .app sigma q a => .app sigma (shiftCode cutoff q) (shiftCode cutoff a)
  | .bottom tau => .bottom tau
  | .ordinary head base => .ordinary head (shiftCode cutoff base)
  | .numbered k head tau base types extras =>
      .numbered k head tau (shiftCode cutoff base) types (shiftCode cutoff extras)
  | .argumentsNil => .argumentsNil
  | .argumentsCons sigma q rest => .argumentsCons sigma (shiftCode cutoff q) (shiftCode cutoff rest)

def prefixWeakening (binders Gamma : List Ty) (sigma : Ty) :
    Renaming (binders++Gamma) (binders++sigma::Gamma) :=
  match binders with
  | [] => Renaming.weaken Gamma sigma
  | _::binders => Renaming.lift (prefixWeakening binders Gamma sigma)

def weakenPacked {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} (sigma : Ty)
    (q : Packed (Fin n) arity Gamma) : Packed (Fin n) arity (sigma::Gamma) :=
  ⟨q.1,rename q.2 (Renaming.weaken Gamma sigma)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShift
