module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransferArithmeticRulesProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransferAgreementProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.Proof
open GorbowSyntax GorbowTheoryProof Hilbert
open LogicLineages.OrdinalComparison.TerminationOrdering
open Syntax Connectives

/-- Structural compilation of EVERY original source rule at falseBody. -/
private noncomputable def localTransport {T : Sentence → Prop} {alpha : Type}
    {Gamma : List (SourceFormula alpha)} {phi : SourceFormula alpha}
    (d : ID1Completion.InternalCalculus.Derivation falseBody Gamma phi) :
    ∀ (m : Nat) (rho : alpha → Term m),
    Local T m (Gamma.map (fun a => translate a rho)) (translate phi rho) := by
  induction d with
  | hypothesis h =>
      intro m rho
      exact .hypothesis (List.mem_map.mpr ⟨_,h,rfl⟩)
  | weakening h d ih =>
      intro m rho
      apply Logic.monotone _ (ih m rho)
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact List.mem_map.mpr ⟨b,h b hb,rfl⟩
  | implicationIntroduction d ih =>
      intro m rho
      exact Local.discharge (ih m rho)
  | implicationElimination d e ihd ihe =>
      intro m rho
      exact .mp (ihd m rho) (ihe m rho)
  | conjunctionIntroduction d e ihd ihe =>
      intro m rho
      rw [translateConjunction]
      exact Logic.pairIntroduction (ihd m rho) (ihe m rho)
  | conjunctionLeft d ih =>
      intro m rho
      exact Logic.pairLeft (by simpa only [translateConjunction] using ih m rho)
  | conjunctionRight d ih =>
      intro m rho
      exact Logic.pairRight (by simpa only [translateConjunction] using ih m rho)
  | explosion d ih =>
      intro m rho
      exact Logic.fromFalse _ (ih m rho)
  | classical d ih =>
      intro m rho
      exact Logic.classical _ (ih m rho)
  | universalIntroduction d ih =>
      intro m rho
      rw [translateAllOne]
      apply Logic.allIntroduction
      simpa only [List.map_map,Function.comp_def,translateWeaken] using ih (m+1) (liftMap rho)
  | universalElimination t d ih =>
      intro m rho
      rw [translateInstantiate]
      exact .mp (.base (.logical (.allInstantiate _ (translateTerm rho t))))
        (by simpa only [translateAllOne] using ih m rho)
  | existentialIntroduction t d ih =>
      intro m rho
      rw [translateExistsOne]
      apply Logic.existentialIntroduction _ (translateTerm rho t)
      simpa only [translateInstantiate] using ih m rho
  | existentialElimination d e ihd ihe =>
      intro m rho
      apply Logic.existentialElimination _ _
      · simpa only [translateExistsOne] using ihd m rho
      · simpa only [List.map_cons,List.map_map,Function.comp_def,translateWeaken]
          using ihe (m+1) (liftMap rho)
  | equalityReflexivity t =>
      intro m rho
      rw [translateEquality]
      exact .base (.logical (.reflexive _))
  | equalityElimination theta t u d e ihd ihe =>
      intro m rho
      rw [translateInstantiate]
      have heq := ihd m rho
      rw [translateEquality] at heq
      have ht := ihe m rho
      rw [translateInstantiate] at ht
      exact .mp (.mp (.base (.logical (.equalityReplace
        (translate theta (liftMap rho)) (translateTerm rho t) (translateTerm rho u)))) heq) ht
  | arithmetic w =>
      intro m rho
      exact .base (ArithmeticRules.arithmetic w rho)
  | inductiveClosure =>
      intro m rho
      rw [PositiveArithmeticSchemas.closureSchema,translateAllOne]
      change Local _ _ _ (.all (.imp falsity falsity))
      exact .base (.generalize (Hilbert.identity falsity))
  | inductiveLeastness theta =>
      intro m rho
      change Local _ _ _ (.imp
        (translate (SourceComputabilityFormulaSupportProof.allOne
          ((PositiveArithmeticPredicateSubstitution.substitutePredicate
            (ID1Completion.InternalCalculus.bodyWithParameters falseBody _)
            (PositiveArithmeticPredicateSubstitution.liftPredicateFormula theta)).imp theta)) rho)
        (translate (SourceComputabilityFormulaSupportProof.allOne
          (PositiveArithmeticSchemas.predicateAtObject.imp theta)) rho))
      rw [translateAllOne,translateAllOne]
      change Local _ _ _ (.imp
        (.all (.imp falsity (translate theta (liftMap rho))))
        (.all (.imp falsity (translate theta (liftMap rho)))))
      exact .base (Hilbert.identity _)

theorem contextTransport : Targets.ContextTransport := by
  intro T alpha Gamma phi m rho h
  obtain ⟨d⟩ := h
  exact ⟨Logic.dischargeAll (localTransport d m rho)⟩

theorem closedArithmeticTransport : Targets.ClosedArithmeticTransport := by
  intro T alpha phi m free h
  obtain ⟨d⟩ := contextTransport T alpha []
    (PositiveArithmeticOperators.arithmeticEmbedding.onFormula phi) m
    (fun a => Term.var (free a)) h
  have hd : Derivation T (translate (PositiveArithmeticOperators.arithmeticEmbedding.onFormula phi)
      (fun a => Term.var (free a))) := by
    simpa only [List.map_nil,closeAssumptions,List.foldr_nil] using d
  have he : translate (PositiveArithmeticOperators.arithmeticEmbedding.onFormula phi)
      (fun a => Term.var (free a)) =
      GorbowOrdinaryArithmeticGraphs.translateBounded phi free Fin.elim0 :=
    Agreement.ordinaryFormulaAgreement alpha phi m free
  exact ⟨cast (congrArg (Derivation T) he) hd⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.Proof
