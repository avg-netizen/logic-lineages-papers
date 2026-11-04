module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulationProof

@[expose] public section
/-! Effective original-source structural translation in one shared source window.
The source anchor supplies S=literalTypes(source) for BOTH endpoints, even when
the target has a smaller type support. Numeric input is decoded using the actual
original syntax presentation; invalid source/target numbers return none. This
does not alter the original comparison relation or add a transitivity closure.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslation
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedOriginalSourcePresentation
open NumberedOriginalSourcePresentationProof NumberedLeastCodeRepresentative NumberedOrdinaryWindow

def packedTranslation {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (p : PackedSource (Fin n) arity Gamma) : Packed (Fin n) arity Gamma :=
  ⟨p.1,translateOriginal p.2⟩

def windowTranslation {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (S : List Ty) (p : PackedSource (Fin n) arity Gamma) : Nat :=
  representativeCode (symbols n) S (packedTranslation p)

def sourceAnchoredCodes {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (source target : PackedSource (Fin n) arity Gamma) : Nat × Nat :=
  (windowTranslation (Source.SourcePortContexts.literalTypes source.2) source,
   windowTranslation (Source.SourcePortContexts.literalTypes source.2) target)

def numericTranslation (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (source target : Nat) : Option (Nat × Nat) := do
  let s ← decodePackedSourceNumber n arity Gamma source
  let t ← decodePackedSourceNumber n arity Gamma target
  pure (sourceAnchoredCodes s t)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslation
