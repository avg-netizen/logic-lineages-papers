module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (cancelSuc zeroNeSuc)
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalNodeSyntaxProof
open OriginalHereditaryValidityInternalNodeSupportProof (weakenProof)
open OriginalHereditaryValidityInternalRecurrenceAcceptanceProof (acceptanceFactors)
open OriginalHereditaryValidityInternalRecurrenceLambdaProof (lambdaRecurrence)
open OriginalHereditaryValidityInternalRecurrenceOutputSupportProof (validatorReject)
open OriginalTransparentLambdaValidityInternal OriginalTransparentLambdaValidityInternalBooleanProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem addAssumption {P : Formula alpha} (h : Nonempty (Derivation body Gamma P)) (q : Formula alpha) :
    Nonempty (Derivation body (q :: Gamma) P) :=
  weakenProof h (fun p hp => List.mem_cons_of_mem q hp)

/-- At literal tag one, the node's application-membership implication is
proved internally impossible. Its actual outer type witness is not supplied. -/
theorem nodeAtLambda (s t m : Program 2) (raw parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (graph2 s (numeral 1) raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 t (numeral 1) raw parameter)))
    (htag : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Delta typ hj htyp
  have hs' := renameInto hs j Delta hj
  have ht' := renameInto ht j Delta hj
  have htag' := renameInto htag j Delta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hs' ht'
  simp only [graph1Rename,numeral,sucRelabel,zRelabel] at htag'
  simp only [consTermRename,emptyRename] at htyp
  simp only [factorsRename]
  let E : Formula beta := equal (numeral 1) (numeral 2)
  have he : Derivation body (E :: Delta) E := Derivation.hypothesis List.mem_cons_self
  have he' : Derivation body (E :: Delta)
      (InternalTagArithmeticSyntaxProof.eqn (suc z) (suc (suc z))) := by
    simpa only [E,equalEqn,numeral] using he
  have hfalse : Derivation body (E :: Delta) ⊥ :=
    zeroNeSuc (cancelSuc he')
  have hm : Nonempty (Derivation body Delta
      (E.imp (graph2 m (numeral 1) typ (parameter.relabel j)))) :=
    ⟨Derivation.implicationIntroduction (Derivation.explosion hfalse)⟩
  exact andIntro hs' (andIntro ht'
    (fieldsIntro m (raw.relabel j) (parameter.relabel j) typ (numeral 1)
      (andIntro htyp (andIntro htag' hm))))

theorem lambdaAcceptanceEquation (s t m : Program 2) (raw parameter : OTerm alpha)
    (F : Formula alpha)
    (htag : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 1) raw)))
    (hnode : Nonempty (Derivation body Gamma ((NodeFactors s t m raw parameter).iff F))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff
        (F ⊓ RootLambdaChild s t m raw parameter))) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  let B := F ⊓ RootLambdaChild s t m raw parameter
  have hf : Nonempty (Derivation body (A :: Gamma) B) := by
    have ha : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hn := acceptanceFactors s t m raw parameter ha
    obtain ⟨he⟩ := lambdaRecurrence s t m raw parameter hn (addAssumption htag A)
    obtain ⟨hnode'⟩ := addAssumption hnode A
    obtain ⟨hn⟩ := hn
    obtain ⟨ha⟩ := ha
    exact ⟨Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (Derivation.conjunctionLeft hnode') hn)
      (Derivation.implicationElimination (Derivation.conjunctionLeft he) ha)⟩
  have hb : Nonempty (Derivation body (B :: Gamma) A) := by
    have h : Derivation body (B :: Gamma) B := Derivation.hypothesis List.mem_cons_self
    obtain ⟨hnode'⟩ := addAssumption hnode B
    have hn : Nonempty (Derivation body (B :: Gamma) (NodeFactors s t m raw parameter)) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hnode') (Derivation.conjunctionLeft h)⟩
    obtain ⟨he⟩ := lambdaRecurrence s t m raw parameter hn (addAssumption htag B)
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight he) (Derivation.conjunctionRight h)⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem lambdaOutputEquation (s t m : Program 2) (out raw parameter : OTerm alpha)
    (F : Formula alpha)
    (htag : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 1) raw)))
    (hnode : Nonempty (Derivation body Gamma ((NodeFactors s t m raw parameter).iff F))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) out raw parameter).iff
        (BooleanOutput out (F ⊓ RootLambdaChild s t m raw parameter)))) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  let B := F ⊓ RootLambdaChild s t m raw parameter
  obtain ⟨he⟩ := lambdaAcceptanceEquation s t m raw parameter F htag hnode
  have hy : Nonempty (Derivation body Gamma (B.imp A)) := ⟨Derivation.conjunctionRight he⟩
  have hn : Nonempty (Derivation body Gamma
      (B.not.imp (graph2 (validator s t m) z raw parameter))) := by
    have hna : Nonempty (Derivation body (B.not :: Gamma) A.not) :=
      ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivation.implicationElimination (addHyp (addHyp (Derivation.conjunctionLeft he) B.not) A)
          (Derivation.hypothesis List.mem_cons_self)))⟩
    obtain ⟨hz⟩ := validatorReject s t m raw parameter hna
    exact ⟨Derivation.implicationIntroduction hz⟩
  exact booleanEquation (validator s t m) (Fin.cons raw (Fin.cons parameter Fin.elim0)) out B hy hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaSupportProof
