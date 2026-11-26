module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionEqualityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem equalSelf (value : OTerm alpha) :
    Nonempty (Derivation body Gamma (equal value value)) := by
  rw [InternalControlGraphSupportProof.equalEqn]
  exact ⟨InternalTagArithmeticSupportProof.refl value⟩

/-- Apply object-language equality at the four inputs of the unchanged
original Program. Its output and every unaltered input remain literal. -/
theorem fourInputs (P : Program 4)
    (out a b c d a' b' c' d' : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma (equal a a')))
    (hb : Nonempty (Derivation body Gamma (equal b b')))
    (hc : Nonempty (Derivation body Gamma (equal c c')))
    (hd : Nonempty (Derivation body Gamma (equal d d')))
    (h : Nonempty (Derivation body Gamma (graph4 P out a b c d))) :
    Nonempty (Derivation body Gamma (graph4 P out a' b' c' d')) := by
  apply graphInputTransport body alpha 4 Gamma (OrdinaryArithmetic.graphFormula P) out
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Fin.elim0))))
    (Fin.cons a' (Fin.cons b' (Fin.cons c' (Fin.cons d' Fin.elim0)))) _ h
  intro i
  exact Fin.cases ha (Fin.cases hb (Fin.cases hc (Fin.cases hd (fun q => Fin.elim0 q)))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeTransportProof
