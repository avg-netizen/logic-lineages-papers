module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfacesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableActionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalPackedCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRawProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (refl symm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaFinalLogicProof
open OriginalFinalVariableCanonicalSupportProof
open OriginalFinalVariableWeakeningSupportProof (compositionEquation)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalRawSyntaxTransportInternalInterfacesProof
open OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
open OriginalRawSyntaxTransportInternalVariableActionProof
open OriginalRawSyntaxTransportInternalPackedProof
open OriginalRawObjectTransportInternalPackedCancellationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Actual cutoff-zero shift of the literal original de Bruijn variable. -/
theorem rawVariableShift (raw shifted index : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (graph1 variableConstructor raw index)))
    (hs : Nonempty (Derivation body Gamma
      (graph1 variableConstructor shifted (OrdinaryArithmetic.succTerm index)))) :
    Nonempty (Derivation body Gamma (graph2 shiftRaw shifted (numeral 0) raw)) := by
  obtain ⟨hn⟩ := InternalBoundedDescentNormalizerStepProof.notLessZero (body := body) (Gamma := Gamma) index
  obtain ⟨hs'⟩ := hs
  have hspec : Nonempty (Derivation body Gamma
      (VariableSpec .shift shifted (numeral 0) (numeral 0) index)) :=
    ⟨InternalQuotientComparisonProof.orRight (Derivation.conjunctionIntroduction hn hs')⟩
  have hf := variableBackward .shift raw shifted (numeral 0) (numeral 0) index hr
    (variableActionSpecBackward .shift shifted (numeral 0) (numeral 0) index hspec)
  exact iffForward (actualRawSyntaxInternalInterfaces body alpha Gamma shifted (numeral 0) (numeral 0) raw).1 hf

/-- The literal packed wrapper preserves the outer type and the all-raw
internal inverse constructs actual erasure back to the original packed raw. -/
theorem packedVariableTransport (raw shifted variableCode shiftedVariable typ index addedType : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (graph1 variableConstructor variableCode index)))
    (hcs : Nonempty (Derivation body Gamma
      (graph1 variableConstructor shiftedVariable (OrdinaryArithmetic.succTerm index))))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hps : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing shifted typ shiftedVariable))) :
    Nonempty (Derivation body Gamma (graph2 shiftPackedRaw shifted (numeral 0) raw)) ∧
    Nonempty (Derivation body Gamma (graph3 erasePackedRaw raw addedType (numeral 0) shifted)) := by
  have hs := shiftPackedBackward raw shifted typ variableCode shiftedVariable (numeral 0) hp
    (rawVariableShift variableCode shiftedVariable index hc hcs) hps
  exact ⟨hs,packedRightInverse raw shifted addedType (numeral 0) hs⟩

/-- All rank outputs are exposed through the original rank interface, its
actual variable branch, and the literal right selector of the packed pair. -/
theorem packedVariableRankEquation (out raw variableCode typ index : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (graph1 variableConstructor variableCode index)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode))) :
    Nonempty (Derivation body Gamma
      ((graph1 variableRankPackedRaw out raw).iff (equal out (numeral 1)))) := by
  have hpacked := compositionEquation variableRankRaw (fun _ : Fin 1 => InternalUnpair.right) out
    (Fin.cons raw Fin.elim0) (Fin.cons variableCode Fin.elim0)
    (fun i => Fin.cases (pairRight raw typ variableCode hp) (fun j => Fin.elim0 j) i)
  have hinterface := (actualRawSyntaxInternalInterfaces body alpha Gamma out (numeral 0) (numeral 0) variableCode).2.2
  obtain ⟨hvariable⟩ := actualRawSyntaxInternalVariable body .rank alpha Gamma variableCode out
    (numeral 0) (numeral 0) index
  obtain ⟨hc'⟩ := hc
  have haction := actualRawSyntaxInternalVariableAction body .rank alpha Gamma out (numeral 0) (numeral 0) index
  exact iffCompose hpacked (iffCompose (iffReverse hinterface)
    (iffCompose ⟨Derivation.implicationElimination hvariable hc'⟩ haction))

/-- Equality transports only the actual third input of the actual Program. -/
theorem thirdTransport (p : Program 3) (out first second source target : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (equal source target)))
    (hg : Nonempty (Derivation body Gamma (graph3 p out first second source))) :
    Nonempty (Derivation body Gamma (graph3 p out first second target)) := by
  apply graphInputTransport body alpha 3 Gamma (OrdinaryArithmetic.graphFormula p) out
    (Fin.cons first (Fin.cons second (Fin.cons source Fin.elim0)))
    (Fin.cons first (Fin.cons second (Fin.cons target Fin.elim0))) _ hg
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · rw [onEquality]; exact ⟨refl first⟩
  · rw [onEquality]; exact ⟨refl second⟩
  · rw [onEquality]
    exact (show Nonempty (Derivation body Gamma (eqn source target)) from
      by simpa only [equalEqn] using he)

/-- Symbolic input equality produces both directions of the same rank graph,
without comparing standard-natural evaluations. -/
theorem rankInputEquation (out source target : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (equal source target))) :
    Nonempty (Derivation body Gamma
      ((graph1 variableRankPackedRaw out source).iff (graph1 variableRankPackedRaw out target))) := by
  let A := graph1 variableRankPackedRaw out source
  let B := graph1 variableRankPackedRaw out target
  obtain ⟨he'⟩ := he
  have heq : Derivation body Gamma (eqn source target) := by simpa only [equalEqn] using he'
  obtain ⟨hf⟩ := headTransport variableRankPackedRaw out source target Fin.elim0
    (addAssumption ⟨heq⟩ A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := headTransport variableRankPackedRaw out target source Fin.elim0
    (addAssumption ⟨symm heq⟩ B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRawProof
