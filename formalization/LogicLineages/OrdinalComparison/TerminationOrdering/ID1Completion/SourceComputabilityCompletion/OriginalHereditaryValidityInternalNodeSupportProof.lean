module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalNodeSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof InternalStructuralEndpointGuardSupportProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem weakenProof {P : Formula α} {Delta : List (Formula α)}
    (h : Nonempty (Derivation body Gamma P)) (inc : ∀ p ∈ Gamma, p ∈ Delta) :
    Nonempty (Derivation body Delta P) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.weakening inc h⟩

theorem exactAccept {n : Nat} (p : Program n) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph p (numeral 1) xs))) :
    Nonempty (Derivation body Gamma (programGraph (exactOne p) (numeral 1) xs)) :=
  sameAccept p (InternalLessThan.constantOne n) (numeral 1) xs h
    (InternalLessThanSupportProof.oneConstantValue xs)

theorem exactRecover {n : Nat} (p : Program n) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (exactOne p) (numeral 1) xs))) :
    Nonempty (Derivation body Gamma (programGraph p (numeral 1) xs)) :=
  sameRightRecover p (InternalLessThan.constantOne n) (numeral 1) xs h
    (InternalLessThanSupportProof.oneConstantValue xs)

theorem equalityCases (x y : OTerm α) (psi : Formula α)
    (kzero : ∀ Delta : List (Formula α), (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 InternalEqualityTest.equalityTest z x y)) →
      Nonempty (Derivation body Delta psi))
    (kone : ∀ Delta : List (Formula α), (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 InternalEqualityTest.equalityTest (suc z) x y)) →
      Nonempty (Derivation body Delta psi)) : Nonempty (Derivation body Gamma psi) := by
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (InternalPositiveUnfoldingSupportProof.weakenClosed cmp Gamma)
  obtain ⟨hl⟩ := kzero (ltF x y :: Gamma) (fun p hp => List.mem_cons_of_mem _ hp)
    (InternalEqualityTestProof.rejectForwardOrder x y ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨he⟩ := kone (eqn x y :: Gamma) (fun p hp => List.mem_cons_of_mem _ hp)
    (InternalEqualityTestCompositionProof.equalityOfEqual x y ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hr⟩ := kzero (ltF y x :: Gamma) (fun p hp => List.mem_cons_of_mem _ hp)
    (InternalEqualityTestProof.rejectBackwardOrder x y ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have rest : Derivation body Gamma ((eqn x y ⊔ ltF y x).imp psi) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction he) _)
      (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) rest⟩

theorem recoverFields (s t m : Program 2) (state raw parameter typ tag : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph1 currentRaw raw state)))
    (hp : Nonempty (Derivation body Gamma (graph1 currentParameter parameter state)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ raw)))
    (hg : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag tag raw)))
    (hn : Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state))) :
    Nonempty (Derivation body Gamma (fields m raw parameter typ tag)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hc := andRight (conjunctionRecover (exactOne (.composition s ![currentRaw,currentParameter])) _ xs hn)
  have hb := andRight (conjunctionRecover (exactOne (.composition t ![currentRaw,currentParameter])) _ xs hc)
  have htyp : Nonempty (Derivation body Gamma (graph1 currentType typ state)) :=
    unaryValue InternalUnpair.left currentRaw typ raw xs ht hr
  have htag : Nonempty (Derivation body Gamma (graph1 currentTag tag state)) :=
    unaryValue OriginalLambdaConstructor.tag currentRaw tag raw xs hg hr
  have hi : Nonempty (Derivation body Gamma ((equal tag (numeral 2)).imp (graph2 m (numeral 1) typ parameter))) := by
    let E := equal tag (numeral 2)
    have he : Nonempty (Derivation body (E :: Gamma) (equal tag (numeral 2))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have htest := binaryValue InternalEqualityTest.equalityTest currentTag (two 1) (numeral 1) tag (numeral 2) xs
      (InternalEqualityTestCompositionProof.equalityOfEqual tag (numeral 2) (by simpa only [equalEqn] using he))
      (weakenProof htag (fun p hp => List.mem_cons_of_mem _ hp)) (twoValue xs)
    have hm := exactRecover (.composition m ![currentType,currentParameter]) xs
      (successorBranchElim _ _ _ (numeral 1) z xs htest
        (weakenProof hb (fun p hp => List.mem_cons_of_mem _ hp)))
    obtain ⟨hm⟩ := binaryRecover m currentType currentParameter (numeral 1) typ parameter xs hm
      (weakenProof htyp (fun p hp => List.mem_cons_of_mem _ hp))
      (weakenProof hp (fun p hp => List.mem_cons_of_mem _ hp))
    exact ⟨Derivation.implicationIntroduction hm⟩
  exact andIntro ht (andIntro hg hi)

theorem acceptAtFields (s t m : Program 2) (state raw parameter typ tag : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph1 currentRaw raw state)))
    (hp : Nonempty (Derivation body Gamma (graph1 currentParameter parameter state)))
    (hs : Nonempty (Derivation body Gamma (graph2 s (numeral 1) raw parameter)))
    (htarget : Nonempty (Derivation body Gamma (graph2 t (numeral 1) raw parameter)))
    (hf : Nonempty (Derivation body Gamma (fields m raw parameter typ tag))) :
    Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have htyp : Nonempty (Derivation body Gamma (graph1 currentType typ state)) :=
    unaryValue InternalUnpair.left currentRaw typ raw xs (andLeft hf) hr
  have htag : Nonempty (Derivation body Gamma (graph1 currentTag tag state)) :=
    unaryValue OriginalLambdaConstructor.tag currentRaw tag raw xs (andLeft (andRight hf)) hr
  apply conjunctionAccept _ _ xs
    (exactAccept _ xs (binaryValue s currentRaw currentParameter (numeral 1) raw parameter xs hs hr hp))
  apply conjunctionAccept _ _ xs
    (exactAccept _ xs (binaryValue t currentRaw currentParameter (numeral 1) raw parameter xs htarget hr hp))
  apply equalityCases tag (numeral 2) _
  · intro Delta inc he
    exact zeroBranchIntro _ _ _ (numeral 1) xs
      (binaryValue InternalEqualityTest.equalityTest currentTag (two 1) z tag (numeral 2) xs he
        (weakenProof htag inc) (twoValue xs)) (InternalLessThanSupportProof.oneConstantValue xs)
  · intro Delta inc he
    have hEq := InternalEqualityTestProof.equalityOfAcceptance tag (numeral 2) he
    obtain ⟨himp⟩ := weakenProof (andRight (andRight hf)) inc
    obtain ⟨hEq⟩ := hEq
    have hm : Nonempty (Derivation body Delta (graph2 m (numeral 1) typ parameter)) :=
      ⟨Derivation.implicationElimination himp (by simpa only [equalEqn] using hEq)⟩
    exact successorBranchIntro _ _ _ (numeral 1) z xs
      (binaryValue InternalEqualityTest.equalityTest currentTag (two 1) (numeral 1) tag (numeral 2) xs he
        (weakenProof htag inc) (twoValue xs))
      (exactAccept _ xs (binaryValue m currentType currentParameter (numeral 1) typ parameter xs hm
        (weakenProof htyp inc) (weakenProof hp inc)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSupportProof
