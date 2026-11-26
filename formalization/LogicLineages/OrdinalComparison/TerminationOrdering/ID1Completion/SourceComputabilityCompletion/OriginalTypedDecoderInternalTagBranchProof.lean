module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalTagBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralIntro branchNumeralElim)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalBranchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def termCase (H : Program 1) : Fin 8 → Program 1 :=
  ![variableStep,lambdaStep,applicationStep,bottomStep,ordinaryStep H,numberedStep H,
    constant 1 0,constant 1 0]

def argumentsCase : Fin 8 → Program 1 :=
  ![constant 1 0,constant 1 0,constant 1 0,constant 1 0,constant 1 0,constant 1 0,nilStep,consStep]

theorem termKnownForward (H : Program 1) (state out : OTerm alpha) :
    ∀ i : Fin 8,
      Nonempty (Derivation body Delta (graph1 tag (numeral i.val) state)) →
      Nonempty (Derivation body Delta (graph1 (termDispatch H) out state)) →
      Nonempty (Derivation body Delta (graph1 (termCase H i) out state)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ht ho
    exact branchNumeralElim 0 0 tag _ _ out (Fin.cons state Fin.elim0) ht ho
  · 
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ht ho
      have h0 := branchNumeralElim 1 0 tag _ _ out (Fin.cons state Fin.elim0) ht ho
      exact branchNumeralElim 1 1 tag _ _ out (Fin.cons state Fin.elim0) ht h0
    · 
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ht ho
        have h0 := branchNumeralElim 2 0 tag _ _ out (Fin.cons state Fin.elim0) ht ho
        have h1 := branchNumeralElim 2 1 tag _ _ out (Fin.cons state Fin.elim0) ht h0
        exact branchNumeralElim 2 2 tag _ _ out (Fin.cons state Fin.elim0) ht h1
      · 
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ht ho
          have h0 := branchNumeralElim 3 0 tag _ _ out (Fin.cons state Fin.elim0) ht ho
          have h1 := branchNumeralElim 3 1 tag _ _ out (Fin.cons state Fin.elim0) ht h0
          have h2 := branchNumeralElim 3 2 tag _ _ out (Fin.cons state Fin.elim0) ht h1
          exact branchNumeralElim 3 3 tag _ _ out (Fin.cons state Fin.elim0) ht h2
        · 
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ht ho
            have h0 := branchNumeralElim 4 0 tag _ _ out (Fin.cons state Fin.elim0) ht ho
            have h1 := branchNumeralElim 4 1 tag _ _ out (Fin.cons state Fin.elim0) ht h0
            have h2 := branchNumeralElim 4 2 tag _ _ out (Fin.cons state Fin.elim0) ht h1
            have h3 := branchNumeralElim 4 3 tag _ _ out (Fin.cons state Fin.elim0) ht h2
            exact branchNumeralElim 4 4 tag _ _ out (Fin.cons state Fin.elim0) ht h3
          · 
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ht ho
              have h0 := branchNumeralElim 5 0 tag _ _ out (Fin.cons state Fin.elim0) ht ho
              have h1 := branchNumeralElim 5 1 tag _ _ out (Fin.cons state Fin.elim0) ht h0
              have h2 := branchNumeralElim 5 2 tag _ _ out (Fin.cons state Fin.elim0) ht h1
              have h3 := branchNumeralElim 5 3 tag _ _ out (Fin.cons state Fin.elim0) ht h2
              have h4 := branchNumeralElim 5 4 tag _ _ out (Fin.cons state Fin.elim0) ht h3
              exact branchNumeralElim 5 5 tag _ _ out (Fin.cons state Fin.elim0) ht h4
            · 
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ht ho
                have h0 := branchNumeralElim 6 0 tag _ _ out (Fin.cons state Fin.elim0) ht ho
                have h1 := branchNumeralElim 6 1 tag _ _ out (Fin.cons state Fin.elim0) ht h0
                have h2 := branchNumeralElim 6 2 tag _ _ out (Fin.cons state Fin.elim0) ht h1
                have h3 := branchNumeralElim 6 3 tag _ _ out (Fin.cons state Fin.elim0) ht h2
                have h4 := branchNumeralElim 6 4 tag _ _ out (Fin.cons state Fin.elim0) ht h3
                exact branchNumeralElim 6 5 tag _ _ out (Fin.cons state Fin.elim0) ht h4
              · 
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ht ho
                  have h0 := branchNumeralElim 7 0 tag _ _ out (Fin.cons state Fin.elim0) ht ho
                  have h1 := branchNumeralElim 7 1 tag _ _ out (Fin.cons state Fin.elim0) ht h0
                  have h2 := branchNumeralElim 7 2 tag _ _ out (Fin.cons state Fin.elim0) ht h1
                  have h3 := branchNumeralElim 7 3 tag _ _ out (Fin.cons state Fin.elim0) ht h2
                  have h4 := branchNumeralElim 7 4 tag _ _ out (Fin.cons state Fin.elim0) ht h3
                  exact branchNumeralElim 7 5 tag _ _ out (Fin.cons state Fin.elim0) ht h4
                · exact Fin.elim0 i

theorem termKnownBackward (H : Program 1) (state out : OTerm alpha) :
    ∀ i : Fin 8,
      Nonempty (Derivation body Delta (graph1 tag (numeral i.val) state)) →
      Nonempty (Derivation body Delta (graph1 (termCase H i) out state)) →
      Nonempty (Derivation body Delta (graph1 (termDispatch H) out state)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ht ho
    apply branchNumeralIntro 0 0 tag _ _ out (Fin.cons state Fin.elim0) ht
    exact ho
  · 
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ht ho
      apply branchNumeralIntro 1 0 tag _ _ out (Fin.cons state Fin.elim0) ht
      apply branchNumeralIntro 1 1 tag _ _ out (Fin.cons state Fin.elim0) ht
      exact ho
    · 
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ht ho
        apply branchNumeralIntro 2 0 tag _ _ out (Fin.cons state Fin.elim0) ht
        apply branchNumeralIntro 2 1 tag _ _ out (Fin.cons state Fin.elim0) ht
        apply branchNumeralIntro 2 2 tag _ _ out (Fin.cons state Fin.elim0) ht
        exact ho
      · 
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ht ho
          apply branchNumeralIntro 3 0 tag _ _ out (Fin.cons state Fin.elim0) ht
          apply branchNumeralIntro 3 1 tag _ _ out (Fin.cons state Fin.elim0) ht
          apply branchNumeralIntro 3 2 tag _ _ out (Fin.cons state Fin.elim0) ht
          apply branchNumeralIntro 3 3 tag _ _ out (Fin.cons state Fin.elim0) ht
          exact ho
        · 
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ht ho
            apply branchNumeralIntro 4 0 tag _ _ out (Fin.cons state Fin.elim0) ht
            apply branchNumeralIntro 4 1 tag _ _ out (Fin.cons state Fin.elim0) ht
            apply branchNumeralIntro 4 2 tag _ _ out (Fin.cons state Fin.elim0) ht
            apply branchNumeralIntro 4 3 tag _ _ out (Fin.cons state Fin.elim0) ht
            apply branchNumeralIntro 4 4 tag _ _ out (Fin.cons state Fin.elim0) ht
            exact ho
          · 
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ht ho
              apply branchNumeralIntro 5 0 tag _ _ out (Fin.cons state Fin.elim0) ht
              apply branchNumeralIntro 5 1 tag _ _ out (Fin.cons state Fin.elim0) ht
              apply branchNumeralIntro 5 2 tag _ _ out (Fin.cons state Fin.elim0) ht
              apply branchNumeralIntro 5 3 tag _ _ out (Fin.cons state Fin.elim0) ht
              apply branchNumeralIntro 5 4 tag _ _ out (Fin.cons state Fin.elim0) ht
              apply branchNumeralIntro 5 5 tag _ _ out (Fin.cons state Fin.elim0) ht
              exact ho
            · 
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ht ho
                apply branchNumeralIntro 6 0 tag _ _ out (Fin.cons state Fin.elim0) ht
                apply branchNumeralIntro 6 1 tag _ _ out (Fin.cons state Fin.elim0) ht
                apply branchNumeralIntro 6 2 tag _ _ out (Fin.cons state Fin.elim0) ht
                apply branchNumeralIntro 6 3 tag _ _ out (Fin.cons state Fin.elim0) ht
                apply branchNumeralIntro 6 4 tag _ _ out (Fin.cons state Fin.elim0) ht
                apply branchNumeralIntro 6 5 tag _ _ out (Fin.cons state Fin.elim0) ht
                exact ho
              · 
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ht ho
                  apply branchNumeralIntro 7 0 tag _ _ out (Fin.cons state Fin.elim0) ht
                  apply branchNumeralIntro 7 1 tag _ _ out (Fin.cons state Fin.elim0) ht
                  apply branchNumeralIntro 7 2 tag _ _ out (Fin.cons state Fin.elim0) ht
                  apply branchNumeralIntro 7 3 tag _ _ out (Fin.cons state Fin.elim0) ht
                  apply branchNumeralIntro 7 4 tag _ _ out (Fin.cons state Fin.elim0) ht
                  apply branchNumeralIntro 7 5 tag _ _ out (Fin.cons state Fin.elim0) ht
                  exact ho
                · exact Fin.elim0 i

theorem argumentsKnownForward (state out : OTerm alpha) :
    ∀ i : Fin 8,
      Nonempty (Derivation body Delta (graph1 tag (numeral i.val) state)) →
      Nonempty (Derivation body Delta (graph1 (argumentsDispatch) out state)) →
      Nonempty (Derivation body Delta (graph1 (argumentsCase i) out state)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ht ho
    have h0 := branchNumeralElim 0 6 tag _ _ out (Fin.cons state Fin.elim0) ht ho
    exact branchNumeralElim 0 7 tag _ _ out (Fin.cons state Fin.elim0) ht h0
  · 
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ht ho
      have h0 := branchNumeralElim 1 6 tag _ _ out (Fin.cons state Fin.elim0) ht ho
      exact branchNumeralElim 1 7 tag _ _ out (Fin.cons state Fin.elim0) ht h0
    · 
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ht ho
        have h0 := branchNumeralElim 2 6 tag _ _ out (Fin.cons state Fin.elim0) ht ho
        exact branchNumeralElim 2 7 tag _ _ out (Fin.cons state Fin.elim0) ht h0
      · 
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ht ho
          have h0 := branchNumeralElim 3 6 tag _ _ out (Fin.cons state Fin.elim0) ht ho
          exact branchNumeralElim 3 7 tag _ _ out (Fin.cons state Fin.elim0) ht h0
        · 
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ht ho
            have h0 := branchNumeralElim 4 6 tag _ _ out (Fin.cons state Fin.elim0) ht ho
            exact branchNumeralElim 4 7 tag _ _ out (Fin.cons state Fin.elim0) ht h0
          · 
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ht ho
              have h0 := branchNumeralElim 5 6 tag _ _ out (Fin.cons state Fin.elim0) ht ho
              exact branchNumeralElim 5 7 tag _ _ out (Fin.cons state Fin.elim0) ht h0
            · 
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ht ho
                exact branchNumeralElim 6 6 tag _ _ out (Fin.cons state Fin.elim0) ht ho
              · 
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ht ho
                  have h0 := branchNumeralElim 7 6 tag _ _ out (Fin.cons state Fin.elim0) ht ho
                  exact branchNumeralElim 7 7 tag _ _ out (Fin.cons state Fin.elim0) ht h0
                · exact Fin.elim0 i

theorem argumentsKnownBackward (state out : OTerm alpha) :
    ∀ i : Fin 8,
      Nonempty (Derivation body Delta (graph1 tag (numeral i.val) state)) →
      Nonempty (Derivation body Delta (graph1 (argumentsCase i) out state)) →
      Nonempty (Derivation body Delta (graph1 (argumentsDispatch) out state)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ht ho
    apply branchNumeralIntro 0 6 tag _ _ out (Fin.cons state Fin.elim0) ht
    apply branchNumeralIntro 0 7 tag _ _ out (Fin.cons state Fin.elim0) ht
    exact ho
  · 
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ht ho
      apply branchNumeralIntro 1 6 tag _ _ out (Fin.cons state Fin.elim0) ht
      apply branchNumeralIntro 1 7 tag _ _ out (Fin.cons state Fin.elim0) ht
      exact ho
    · 
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ht ho
        apply branchNumeralIntro 2 6 tag _ _ out (Fin.cons state Fin.elim0) ht
        apply branchNumeralIntro 2 7 tag _ _ out (Fin.cons state Fin.elim0) ht
        exact ho
      · 
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ht ho
          apply branchNumeralIntro 3 6 tag _ _ out (Fin.cons state Fin.elim0) ht
          apply branchNumeralIntro 3 7 tag _ _ out (Fin.cons state Fin.elim0) ht
          exact ho
        · 
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ht ho
            apply branchNumeralIntro 4 6 tag _ _ out (Fin.cons state Fin.elim0) ht
            apply branchNumeralIntro 4 7 tag _ _ out (Fin.cons state Fin.elim0) ht
            exact ho
          · 
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ht ho
              apply branchNumeralIntro 5 6 tag _ _ out (Fin.cons state Fin.elim0) ht
              apply branchNumeralIntro 5 7 tag _ _ out (Fin.cons state Fin.elim0) ht
              exact ho
            · 
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ht ho
                apply branchNumeralIntro 6 6 tag _ _ out (Fin.cons state Fin.elim0) ht
                exact ho
              · 
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ht ho
                  apply branchNumeralIntro 7 6 tag _ _ out (Fin.cons state Fin.elim0) ht
                  apply branchNumeralIntro 7 7 tag _ _ out (Fin.cons state Fin.elim0) ht
                  exact ho
                · exact Fin.elim0 i

theorem termUnknownForward (H : Program 1) (state out value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hn : Nonempty (Derivation body Delta (StepUnknownTag value)))
    (ho : Nonempty (Derivation body Delta (graph1 (termDispatch H) out state))) :
    Nonempty (Derivation body Delta (equal out (numeral 0))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have h0 := sameNoElim tag (constant 1 0) (variableStep) _ out value (numeral 0) xs
    ht (constantValue 0 xs) (andLeft (hn)) ho
  have h1 := sameNoElim tag (constant 1 1) (lambdaStep) _ out value (numeral 1) xs
    ht (constantValue 1 xs) (andLeft (andRight (hn))) h0
  have h2 := sameNoElim tag (constant 1 2) (applicationStep) _ out value (numeral 2) xs
    ht (constantValue 2 xs) (andLeft (andRight (andRight (hn)))) h1
  have h3 := sameNoElim tag (constant 1 3) (bottomStep) _ out value (numeral 3) xs
    ht (constantValue 3 xs) (andLeft (andRight (andRight (andRight (hn))))) h2
  have h4 := sameNoElim tag (constant 1 4) (ordinaryStep H) _ out value (numeral 4) xs
    ht (constantValue 4 xs) (andLeft (andRight (andRight (andRight (andRight (hn)))))) h3
  have h5 := sameNoElim tag (constant 1 5) (numberedStep H) _ out value (numeral 5) xs
    ht (constantValue 5 xs) (andLeft (andRight (andRight (andRight (andRight (andRight (hn))))))) h4
  exact constantForward 0 out xs h5

theorem termUnknownBackward (H : Program 1) (state out value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hn : Nonempty (Derivation body Delta (StepUnknownTag value)))
    (ho : Nonempty (Derivation body Delta (equal out (numeral 0)))) :
    Nonempty (Derivation body Delta (graph1 (termDispatch H) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply sameNoIntro tag (constant 1 0) (variableStep) _ out value (numeral 0) xs
    ht (constantValue 0 xs) (andLeft (hn))
  apply sameNoIntro tag (constant 1 1) (lambdaStep) _ out value (numeral 1) xs
    ht (constantValue 1 xs) (andLeft (andRight (hn)))
  apply sameNoIntro tag (constant 1 2) (applicationStep) _ out value (numeral 2) xs
    ht (constantValue 2 xs) (andLeft (andRight (andRight (hn))))
  apply sameNoIntro tag (constant 1 3) (bottomStep) _ out value (numeral 3) xs
    ht (constantValue 3 xs) (andLeft (andRight (andRight (andRight (hn)))))
  apply sameNoIntro tag (constant 1 4) (ordinaryStep H) _ out value (numeral 4) xs
    ht (constantValue 4 xs) (andLeft (andRight (andRight (andRight (andRight (hn))))))
  apply sameNoIntro tag (constant 1 5) (numberedStep H) _ out value (numeral 5) xs
    ht (constantValue 5 xs) (andLeft (andRight (andRight (andRight (andRight (andRight (hn)))))))
  exact constantBackward 0 out xs ho

theorem argumentsUnknownForward (state out value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hn : Nonempty (Derivation body Delta (StepUnknownTag value)))
    (ho : Nonempty (Derivation body Delta (graph1 argumentsDispatch out state))) :
    Nonempty (Derivation body Delta (equal out (numeral 0))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have htail := andRight (andRight (andRight (andRight (andRight (andRight hn)))))
  have h6 := sameNoElim tag (constant 1 6) nilStep _ out value (numeral 6) xs
    ht (constantValue 6 xs) (andLeft htail) ho
  have h7 := sameNoElim tag (constant 1 7) consStep _ out value (numeral 7) xs
    ht (constantValue 7 xs) (andRight htail) h6
  exact constantForward 0 out xs h7

theorem argumentsUnknownBackward (state out value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 tag value state)))
    (hn : Nonempty (Derivation body Delta (StepUnknownTag value)))
    (ho : Nonempty (Derivation body Delta (equal out (numeral 0)))) :
    Nonempty (Derivation body Delta (graph1 argumentsDispatch out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have htail := andRight (andRight (andRight (andRight (andRight (andRight hn)))))
  apply sameNoIntro tag (constant 1 6) nilStep _ out value (numeral 6) xs
    ht (constantValue 6 xs) (andLeft htail)
  apply sameNoIntro tag (constant 1 7) consStep _ out value (numeral 7) xs
    ht (constantValue 7 xs) (andRight htail)
  exact constantBackward 0 out xs ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalTagBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalTagBranchProof
