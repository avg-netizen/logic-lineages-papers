module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalHereditaryValidityInternalNodeSupportProof (equalityCases weakenProof)
open InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalQuotientComparisonProof (orLeft orRight)
open InternalControlGraphChoiceProof (excludedMiddle)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem sameLeftRecover {n : Nat} (p q : Program n) (value : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hs : Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same p q) (numeral 1) xs)))
    (hp : Nonempty (Derivation body Gamma (programGraph p value xs))) :
    Nonempty (Derivation body Gamma (programGraph q value xs)) := by
  apply programCases q xs _
  intro beta j Delta right hj hq
  have hs' := renameInto hs j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [programRename,numeral,sucRelabel,zRelabel] at hs' hp'
  simp only [programRename]
  obtain ⟨he⟩ := InternalEqualityTestProof.equalityOfAcceptance (value.relabel j) right
    (binaryRecover InternalEqualityTest.equalityTest p q (numeral 1)
      (value.relabel j) right (fun i => (xs i).relabel j) hs' hp' hq)
  exact outputTransport q right (value.relabel j) (fun i => (xs i).relabel j) ⟨symm he⟩ hq

theorem sameReject {n : Nat} (p q : Program n) (xs : Fin n → OTerm alpha)
    (hn : Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same p q) (numeral 1) xs).not)) :
    Nonempty (Derivation body Gamma
      (programGraph (InternalApplicationStepPeel.same p q) z xs)) := by
  apply queryCases ![p,q] xs _
  intro beta j ys Delta hj hq
  have hn' := renameInto hn j Delta hj
  change Nonempty (Derivation body Delta
    ((programGraph (InternalApplicationStepPeel.same p q) (numeral 1) xs).relabel j).not) at hn'
  simp only [programRename,numeral,sucRelabel,zRelabel] at hn'
  simp only [programRename,zRelabel]
  apply equalityCases (ys 0) (ys 1) _
  · intro Theta inc he
    exact binaryValue InternalEqualityTest.equalityTest p q z (ys 0) (ys 1)
      (fun i => (xs i).relabel j) he (weakenProof (hq 0) inc) (weakenProof (hq 1) inc)
  · intro Theta inc he
    obtain ⟨ha⟩ := binaryValue InternalEqualityTest.equalityTest p q (numeral 1) (ys 0) (ys 1)
      (fun i => (xs i).relabel j) he (weakenProof (hq 0) inc) (weakenProof (hq 1) inc)
    obtain ⟨hn''⟩ := weakenProof hn' inc
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn'' ha)⟩

/-- Two internally proved branch implications determine every output by
original Program functionality. No semantic Boolean-range fact is used. -/
theorem booleanEquation {n : Nat} (p : Program n) (xs : Fin n → OTerm alpha)
    (out : OTerm alpha) (accepted : Formula alpha)
    (hyes : Nonempty (Derivation body Gamma
      (accepted.imp (programGraph p (numeral 1) xs))))
    (hno : Nonempty (Derivation body Gamma
      (accepted.not.imp (programGraph p z xs)))) :
    Nonempty (Derivation body Gamma
      ((programGraph p out xs).iff (BooleanOutput out accepted))) := by
  obtain ⟨hy⟩ := hyes
  obtain ⟨hn⟩ := hno
  let G := programGraph p out xs
  let L := equal out (numeral 1) ⊓ accepted
  let R := equal out z ⊓ accepted.not
  have hf : Nonempty (Derivation body (G :: Gamma) (BooleanOutput out accepted)) := by
    have hl : Nonempty (Derivation body (accepted :: G :: Gamma) (BooleanOutput out accepted)) := by
      have hp := Derivation.implicationElimination (addHyp (addHyp hy G) accepted)
        (Derivation.hypothesis List.mem_cons_self)
      obtain ⟨he⟩ := valueUnique p out (numeral 1) xs
        (show Nonempty (Derivation body (accepted :: G :: Gamma) G) from
          ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩) ⟨hp⟩
      exact ⟨orLeft (Derivation.conjunctionIntroduction
        (by simpa only [equalEqn] using he) (Derivation.hypothesis List.mem_cons_self))⟩
    have hr : Nonempty (Derivation body (accepted.not :: G :: Gamma) (BooleanOutput out accepted)) := by
      have hp := Derivation.implicationElimination (addHyp (addHyp hn G) accepted.not)
        (Derivation.hypothesis List.mem_cons_self)
      obtain ⟨he⟩ := valueUnique p out z xs
        (show Nonempty (Derivation body (accepted.not :: G :: Gamma) G) from
          ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩) ⟨hp⟩
      exact ⟨orRight (Derivation.conjunctionIntroduction
        (by simpa only [equalEqn] using he) (Derivation.hypothesis List.mem_cons_self))⟩
    obtain ⟨hl⟩ := hl
    obtain ⟨hr⟩ := hr
    exact ⟨disjunctionElimination (excludedMiddle accepted)
      (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩
  have hl : Nonempty (Derivation body (L :: Gamma) G) := by
    have h : Derivation body (L :: Gamma) L := Derivation.hypothesis List.mem_cons_self
    have hp := Derivation.implicationElimination (addHyp hy L) (Derivation.conjunctionRight h)
    obtain ⟨hg⟩ := outputTransport p (numeral 1) out xs
      ⟨symm (by simpa only [equalEqn] using Derivation.conjunctionLeft h)⟩ ⟨hp⟩
    exact ⟨hg⟩
  have hr : Nonempty (Derivation body (R :: Gamma) G) := by
    have h : Derivation body (R :: Gamma) R := Derivation.hypothesis List.mem_cons_self
    have hp := Derivation.implicationElimination (addHyp hn R) (Derivation.conjunctionRight h)
    obtain ⟨hg⟩ := outputTransport p z out xs
      ⟨symm (by simpa only [equalEqn] using Derivation.conjunctionLeft h)⟩ ⟨hp⟩
    exact ⟨hg⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hl⟩ := hl
  obtain ⟨hr⟩ := hr
  have hb : Derivation body (BooleanOutput out accepted :: Gamma) G :=
    disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction hl) _)
      (addHyp (Derivation.implicationIntroduction hr) _)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
