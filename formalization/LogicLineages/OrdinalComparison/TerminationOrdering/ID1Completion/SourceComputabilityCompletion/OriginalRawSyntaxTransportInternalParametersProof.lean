module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParameters
open OriginalRawSyntaxTransportInternalParametersSyntaxProof OriginalRawSyntaxTransportInternalParametersBindingProof
open OriginalRawSyntaxTransportInternalParametersIntroductionProof OriginalRawSyntaxTransportInternalParametersFieldQueriesProof
open OriginalRawSyntaxTransportInternalParametersLeafProof OriginalRawSyntaxTransportInternalParametersUnaryProof
open OriginalRawSyntaxTransportInternalParametersBinaryProof OriginalRawSyntaxTransportInternalConstructorArityCasesProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem parameterStep (rank : Bool) (raw out d k other otherK : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (selectedMode rank)) rank raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold (selectedMode rank)) out d k raw))) :
    Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode rank)) out other (if rank then otherK else k) raw)) := by
  apply arityCases raw
  · intro beta j Theta hj ha
    simp only [graph3Rename,cutoffChoiceRename]
    have hs' := renameInto hs j Theta hj
    rw [graph3Rename] at hs'
    exact leafParameters rank (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j)
      (other.relabel j) (otherK.relabel j) ha hs'
  · intro beta j Theta hj ha
    simp only [graph3Rename,cutoffChoiceRename]
    have hi' := renameInto hi j Theta hj
    have hs' := renameInto hs j Theta hj
    rw [belowRawRename] at hi'
    rw [graph3Rename] at hs'
    exact unaryParameters rank (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j)
      (other.relabel j) (otherK.relabel j) hi' ha hs'
  · intro beta j Theta hj ha
    simp only [graph3Rename,cutoffChoiceRename]
    have hi' := renameInto hi j Theta hj
    have hs' := renameInto hs j Theta hj
    rw [belowRawRename] at hi'
    rw [graph3Rename] at hs'
    exact binaryParameters rank (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j)
      (other.relabel j) (otherK.relabel j) hi' ha hs'

/-- Parameter independence on ALL arithmetic raw inputs follows by genuine
internal strong induction and the original bounded machine recurrences. -/
theorem allRawParameters (rank : Bool) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw (fold (selectedMode rank)) rank raw)) := by
  apply rawInduction (fold (selectedMode rank)) rank raw
  intro beta Theta r hi
  apply atRawIntroFrom (fold (selectedMode rank)) rank r
  intro gamma j Xi out d k other otherK hj hs
  have hi' := renameInto hi j Xi hj
  rw [belowRawRename] at hi'
  exact parameterStep rank (r.relabel j) out d k other otherK hi' hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersProof
