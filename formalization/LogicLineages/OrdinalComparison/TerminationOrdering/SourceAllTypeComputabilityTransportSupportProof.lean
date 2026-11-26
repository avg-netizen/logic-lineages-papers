module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSingleBottomLeastProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportSupportProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse

theorem singleBottomConfinement {n : Nat} {arity : Fin n → Nat}
    (symbols : List (Fin n)) (S : List Ty) (Gamma : List Ty) (sigma tau : Ty)
    (q : AuxTerm (Fin n) arity (sigma :: Gamma) tau) (hq : InUniverse symbols S q) :
    InUniverse symbols S (substitute q (singleSubstitution (.bottom sigma))) := by
  exact NumberedUniverseBindingProof.substituteGood (fun t => t ∈ S)
    (HeadInWindow arity symbols S) q Gamma (singleSubstitution (.bottom sigma)) hq
    (NumberedBottomVariableProof.actualBottomOrVariableGood (Fin n) arity
      (fun t => t ∈ S) (HeadInWindow arity symbols S) (sigma :: Gamma) Gamma
      (singleSubstitution (.bottom sigma))
      (NumberedBottomVariableProof.actualSingleBottomOrVariable (Fin n) arity Gamma sigma))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportSupportProof
