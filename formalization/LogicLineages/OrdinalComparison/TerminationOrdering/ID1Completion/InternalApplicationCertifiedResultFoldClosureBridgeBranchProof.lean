module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalApplicationResultStackReturnSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalQuotientComparisonProof
open InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nonzeroBranchElim {n : Nat} (control a b : Program n) (out c : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control c xs)))
    (hn : Nonempty (Derivation body Gamma (eqn c z).not))
    (hw : Nonempty (Derivation body Gamma (programGraph (InternalAcceptance.branch control a b) out xs))) :
    Nonempty (Derivation body Gamma (programGraph b out xs)) := by
  apply programCases b xs _
  intro β j Delta v hj hv
  rw [programRename]
  have hc' := InternalGraphCompositionFunctionalityProof.renameInto hc j Delta hj
  have hn' := InternalGraphCompositionFunctionalityProof.renameInto hn j Delta hj
  have hw' := InternalGraphCompositionFunctionalityProof.renameInto hw j Delta hj
  simp only [programRename] at hc' hw'
  simp only [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  have hb := nonzeroBranchIntro control a b v (c.relabel j) (fun i => (xs i).relabel j)
    hc' (by simpa only [equalEqn] using hn') hv
  obtain ⟨he⟩ := valueUnique (InternalAcceptance.branch control a b) v (out.relabel j)
    (fun i => (xs i).relabel j) hb hw'
  exact outputTransport b v (out.relabel j) (fun i => (xs i).relabel j) ⟨he⟩ hv

theorem rejectZeroRecover {n : Nat} (control b : Program n) (c : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control c xs)))
    (hw : Nonempty (Derivation body Gamma
      (programGraph (InternalAcceptance.branch control (InternalAcceptance.constantZero n) b) (suc z) xs))) :
    Nonempty (Derivation body Gamma ((eqn c z).not ⊓ programGraph b (suc z) xs)) := by
  have hn : Nonempty (Derivation body Gamma (eqn c z).not) := by
    have hz := outputTransport control c z xs ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hc (eqn c z))
    have hf := zeroBranchElim control (InternalAcceptance.constantZero n) b (suc z) xs hz
      (withHyp hw (eqn c z))
    obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero n) (suc z) z xs hf (constantZeroValue xs)
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩
  exact andIntro hn (nonzeroBranchElim control _ b (suc z) c xs hc hn hw)

theorem rejectNonzeroRecover {n : Nat} (control a : Program n) (c : OTerm α)
    (xs : Fin n → OTerm α)
    (hc : Nonempty (Derivation body Gamma (programGraph control c xs)))
    (hw : Nonempty (Derivation body Gamma
      (programGraph (InternalAcceptance.branch control a (InternalAcceptance.constantZero n)) (suc z) xs))) :
    Nonempty (Derivation body Gamma (programGraph control z xs ⊓ programGraph a (suc z) xs)) := by
  apply formulaCases (eqn c z)
  · have hz := outputTransport control c z xs ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hc _)
    exact andIntro hz (zeroBranchElim control a _ (suc z) xs hz (withHyp hw _))
  · have hf := nonzeroBranchElim control a (InternalAcceptance.constantZero n) (suc z) c xs
      (withHyp hc _) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hw _)
    obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero n) (suc z) z xs hf (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

theorem equalityOfNonzero (x y c : OTerm α)
    (h : Nonempty (Derivation body Gamma (InternalEqualityTestCompositionProof.equalityGraph c x y)))
    (hn : Nonempty (Derivation body Gamma (eqn c z).not)) :
    Nonempty (Derivation body Gamma (eqn x y)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hn⟩ := hn
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Gamma)
  have hl : Nonempty (Derivation body (ltF x y :: Gamma) (eqn x y)) := by
    have hz := InternalEqualityTestProof.rejectForwardOrder (body := body) (Gamma := _ :: Gamma) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique InternalEqualityTest.equalityTest c z (Fin.cons x (Fin.cons y Fin.elim0))
      ⟨addHyp h _⟩ hz
    exact ⟨Derivation.explosion (Derivation.implicationElimination (addHyp hn _) he)⟩
  have hr : Nonempty (Derivation body (ltF y x :: Gamma) (eqn x y)) := by
    have hz := InternalEqualityTestProof.rejectBackwardOrder (body := body) (Gamma := _ :: Gamma) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := valueUnique InternalEqualityTest.equalityTest c z (Fin.cons x (Fin.cons y Fin.elim0))
      ⟨addHyp h _⟩ hz
    exact ⟨Derivation.explosion (Derivation.implicationElimination (addHyp hn _) he)⟩
  obtain ⟨hl⟩ := hl
  obtain ⟨hr⟩ := hr
  have he : Derivation body Gamma ((eqn x y).imp (eqn x y)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  have hrest : Derivation body Gamma ((eqn x y ⊔ ltF y x).imp (eqn x y)) :=
    Derivation.implicationIntroduction (disjunctionElimination
      (Derivation.hypothesis List.mem_cons_self) (addHyp he _) (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) hrest⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
