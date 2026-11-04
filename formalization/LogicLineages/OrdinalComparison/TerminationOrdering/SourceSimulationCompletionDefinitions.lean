module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslationDefinitions

@[expose] public section
/-! Paper06's translation is a family indexed by a fixed finite type universe.
The SAME member of the family translates both endpoints of a comparison.
The finite signature size, its arity function, and the ambient typed context
are fixed parameters of each effective presentation, not encoded inputs.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletion
open Source NumberedOriginalSourcePresentation NumberedOriginalStructuralTranslation

/-- The actual original-source translation into least primary-equivalence codes
in the fixed universe `S`. It is independent of the other comparison endpoint. -/
def tr {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (S : List Ty) (source : PackedSource (Fin n) arity Gamma) : Nat :=
  windowTranslation S source

/-- The separate numerical interface rejects malformed original-source codes.
This convention imposes no premise on the typed-source simulation theorem. -/
def numericTr (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (S : List Ty) (source : Nat) : Option Nat :=
  (decodePackedSourceNumber n arity Gamma source).map (tr S)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSimulationCompletion
