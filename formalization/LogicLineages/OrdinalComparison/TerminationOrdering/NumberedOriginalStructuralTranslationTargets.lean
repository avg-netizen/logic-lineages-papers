module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslationDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslationTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedOriginalSourcePresentation
open NumberedOriginalSourcePresentationProof NumberedOriginalStructuralTranslation
open NumberedConfinedSourceSimulation NumberedQuotientPaths NumberedOrdinaryWindow LiteralContexts

def ActualOriginalTranslationPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (@packedTranslation n arity Gamma)

def ActualWindowTranslationPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (fun p : List Ty × PackedSource (Fin n) arity Gamma => windowTranslation p.1 p.2)

def ActualSharedWindowPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (fun p : PackedSource (Fin n) arity Gamma × PackedSource (Fin n) arity Gamma => sourceAnchoredCodes p.1 p.2)

def ActualNumericTranslationPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec₂ (numericTranslation n arity Gamma)

def ActualNumericCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (source target : PackedSource (Fin n) arity Gamma),
  numericTranslation n arity Gamma (packedSourceNumber source) (packedSourceNumber target)=
    some (sourceAnchoredCodes source target)

def ActualComputedConfinedSimulation : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (above : Fin n → Fin n → Prop) (Gamma : List Ty) (tau : Ty)
    (s t : Term (Fin n) arity Gamma tau), ConfinedStrict above s t →
  PositivePath (QuotientEdge n arity (symbols n) (sourceWindow s) above Gamma)
    (sourceAnchoredCodes ⟨tau,s⟩ ⟨tau,t⟩).1
    (sourceAnchoredCodes ⟨tau,s⟩ ⟨tau,t⟩).2

def ActualGenuineComputedSimulation : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ tr : PackedSource (Fin n) arity Gamma × PackedSource (Fin n) arity Gamma → Nat × Nat,
    Computable tr ∧
    (∀ source target, tr (source,target)=sourceAnchoredCodes source target) ∧
    (∀ (above : Fin n → Fin n → Prop) (tau : Ty) (s t : Term (Fin n) arity Gamma tau),
      ConfinedStrict above s t →
      PositivePath (QuotientEdge n arity (symbols n) (sourceWindow s) above Gamma)
        (tr (⟨tau,s⟩,⟨tau,t⟩)).1 (tr (⟨tau,s⟩,⟨tau,t⟩)).2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalStructuralTranslationTargets
