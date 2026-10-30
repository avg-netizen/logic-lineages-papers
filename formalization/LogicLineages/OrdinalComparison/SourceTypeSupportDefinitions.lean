module

public import LogicLineages.OrdinalComparison.SourceTerms
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Fin

@[expose] public section
/-! Literal paper06 syntax prerequisites, on the existing typed de Bruijn
kernel. No marked comparison, named-source translation or WW assignment is
assumed. Unused context types are not inserted into a term's support. -/
namespace LogicLineages.OrdinalComparison.Source.SourceTypeSupport

def typeSupport {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : Finset Ty :=
  τ.subtypes.toFinset ∪ match t with
  | .var _ => ∅
  | .app f a => typeSupport f ∪ typeSupport a
  | .lam body => typeSupport body
  | .zeroC => ∅
  | .succC => ∅
  | .caseC _ => ∅
  | .recC _ => ∅
  | .ranked s args => Finset.univ.biUnion fun i : Fin (arity s) => typeSupport (args i)

def lambdaDepth {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : Nat :=
  match t with
  | .var _ => 0
  | .app f a => max (lambdaDepth f) (lambdaDepth a)
  | .lam body => lambdaDepth body + 1
  | .zeroC => 0
  | .succC => 0
  | .caseC _ => 0
  | .recC _ => 0
  | .ranked s args => Finset.univ.sup fun i : Fin (arity s) => lambdaDepth (args i)

end LogicLineages.OrdinalComparison.Source.SourceTypeSupport
