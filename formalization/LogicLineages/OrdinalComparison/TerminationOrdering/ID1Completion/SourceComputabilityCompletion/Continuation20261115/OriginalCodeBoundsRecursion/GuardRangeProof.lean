module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.GuardRangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn z suc)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 HeadWindowBooleanRange HeadWindowBooleanRange.ProgramRangeProof
open HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
attribute [local irreducible] programGraph

theorem equalityRange : Ranged InternalEqualityTest.equalityTest := by
  intro body alpha Delta out xs ho
  have hx : Fin.cons (xs 0) (Fin.cons (xs 1) Fin.elim0) = xs := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  apply formulaCases (eqn (xs 0) (xs 1))
  · have hv := InternalEqualityTestCompositionProof.equalityOfEqual (xs 0) (xs 1)
      (body := body) (Gamma := eqn (xs 0) (xs 1) :: Delta)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    unfold graph2 at hv
    rw [hx] at hv
    obtain ⟨he⟩ := valueUnique InternalEqualityTest.equalityTest out (suc z) xs
      (withHyp ho (eqn (xs 0) (xs 1))) hv
    exact ⟨InternalQuotientComparisonProof.orRight he⟩
  · have hv := OriginalVariableDecoderEqualityProof.equalityReject (xs 0) (xs 1)
      (body := body) (Delta := (eqn (xs 0) (xs 1)).not :: Delta)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    unfold graph2 at hv
    rw [hx] at hv
    obtain ⟨he⟩ := valueUnique InternalEqualityTest.equalityTest out z xs
      (withHyp ho (eqn (xs 0) (xs 1)).not) hv
    exact ⟨InternalQuotientComparisonProof.orLeft he⟩

theorem sameRange {m : Nat} (p q : Program m) : Ranged (OriginalRawSyntaxTransport.sameOf p q) :=
  compositionRange _ _ equalityRange

theorem chooseRange (k : Nat) (yes no : Program 2) (hy : Ranged yes) (hn : Ranged no) :
    Ranged (OriginalCodeDecoderStep.choose k yes no) := branchRange _ _ _ hn hy

theorem stepRange (n : Nat) : Ranged (OriginalCodeDecoderStep.step n) :=
  chooseRange _ _ _ (constantRange 2 1)
    (chooseRange _ _ _ (sameRange _ _)
      (chooseRange _ _ _ (conjunctionRange _ _)
        (chooseRange _ _ _ (constantRange 2 1)
          (chooseRange _ _ _ (conjunctionRange _ _)
            (chooseRange _ _ _ (conjunctionRange _ _)
              (chooseRange _ _ _ (sameRange _ _)
                (chooseRange _ _ _ (conjunctionRange _ _) (constantRange 2 0))))))))

theorem guardRange (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) out raw))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply OriginalCodeValidityConstructors.Proof.tableCases n raw
  intro beta j Theta previous table hj hp ht
  rw [booleanRename]
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  rw [graph1Rename] at hoj
  have hr := OriginalCodeValidityGuard.TableSupportProof.nextRowRecover n (raw.relabel j) (raw.relabel j) previous table hp ht
  have hl := OriginalCodeValidityConstructors.SupportProof.checkRecover n (raw.relabel j) table (out.relabel j) ht hoj
  have hs := OriginalCodeDecoderTable.Proof.internalRowLookup n body beta Theta
    (raw.relabel j) previous table (raw.relabel j) (out.relabel j) hr
    (OriginalCodeValidityConstructors.ChildProof.selfBound (raw.relabel j)) hl
  exact stepRange n body beta Theta (out.relabel j) ![previous,raw.relabel j] hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.GuardRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.GuardRangeProof
