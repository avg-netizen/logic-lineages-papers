module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem tag0Intro (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 0) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (variableBranch) out xs))) :
    Nonempty (Derivation body Delta (programGraph (choose n) out xs)) := by
  unfold choose
  apply branchNumeralIntro 0 0 tag _ _ out xs ht
  exact ho

theorem tag0Elim (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 0) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (choose n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (variableBranch) out xs)) := by
  have h0 := branchNumeralElim 0 0 tag _ _ out xs ht ho
  exact h0

theorem tag1Intro (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 1) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (lambdaBranch) out xs))) :
    Nonempty (Derivation body Delta (programGraph (choose n) out xs)) := by
  unfold choose
  apply branchNumeralIntro 1 0 tag _ _ out xs ht
  apply branchNumeralIntro 1 1 tag _ _ out xs ht
  exact ho

theorem tag1Elim (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 1) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (choose n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (lambdaBranch) out xs)) := by
  have h0 := branchNumeralElim 1 0 tag _ _ out xs ht ho
  have h1 := branchNumeralElim 1 1 tag _ _ out xs ht h0
  exact h1

theorem tag2Intro (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 2) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (binaryBranch) out xs))) :
    Nonempty (Derivation body Delta (programGraph (choose n) out xs)) := by
  unfold choose
  apply branchNumeralIntro 2 0 tag _ _ out xs ht
  apply branchNumeralIntro 2 1 tag _ _ out xs ht
  apply branchNumeralIntro 2 2 tag _ _ out xs ht
  exact ho

theorem tag2Elim (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 2) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (choose n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (binaryBranch) out xs)) := by
  have h0 := branchNumeralElim 2 0 tag _ _ out xs ht ho
  have h1 := branchNumeralElim 2 1 tag _ _ out xs ht h0
  have h2 := branchNumeralElim 2 2 tag _ _ out xs ht h1
  exact h2

theorem tag3Intro (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 3) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (bottomBranch) out xs))) :
    Nonempty (Derivation body Delta (programGraph (choose n) out xs)) := by
  unfold choose
  apply branchNumeralIntro 3 0 tag _ _ out xs ht
  apply branchNumeralIntro 3 1 tag _ _ out xs ht
  apply branchNumeralIntro 3 2 tag _ _ out xs ht
  apply branchNumeralIntro 3 3 tag _ _ out xs ht
  exact ho

theorem tag3Elim (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 3) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (choose n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (bottomBranch) out xs)) := by
  have h0 := branchNumeralElim 3 0 tag _ _ out xs ht ho
  have h1 := branchNumeralElim 3 1 tag _ _ out xs ht h0
  have h2 := branchNumeralElim 3 2 tag _ _ out xs ht h1
  have h3 := branchNumeralElim 3 3 tag _ _ out xs ht h2
  exact h3

theorem tag4Intro (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 4) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (ordinaryBranch n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (choose n) out xs)) := by
  unfold choose
  apply branchNumeralIntro 4 0 tag _ _ out xs ht
  apply branchNumeralIntro 4 1 tag _ _ out xs ht
  apply branchNumeralIntro 4 2 tag _ _ out xs ht
  apply branchNumeralIntro 4 3 tag _ _ out xs ht
  apply branchNumeralIntro 4 4 tag _ _ out xs ht
  exact ho

theorem tag4Elim (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 4) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (choose n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (ordinaryBranch n) out xs)) := by
  have h0 := branchNumeralElim 4 0 tag _ _ out xs ht ho
  have h1 := branchNumeralElim 4 1 tag _ _ out xs ht h0
  have h2 := branchNumeralElim 4 2 tag _ _ out xs ht h1
  have h3 := branchNumeralElim 4 3 tag _ _ out xs ht h2
  have h4 := branchNumeralElim 4 4 tag _ _ out xs ht h3
  exact h4

theorem tag5Intro (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 5) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (numberedBranch n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (choose n) out xs)) := by
  unfold choose
  apply branchNumeralIntro 5 0 tag _ _ out xs ht
  apply branchNumeralIntro 5 1 tag _ _ out xs ht
  apply branchNumeralIntro 5 2 tag _ _ out xs ht
  apply branchNumeralIntro 5 3 tag _ _ out xs ht
  apply branchNumeralIntro 5 4 tag _ _ out xs ht
  apply branchNumeralIntro 5 5 tag _ _ out xs ht
  exact ho

theorem tag5Elim (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 5) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (choose n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (numberedBranch n) out xs)) := by
  have h0 := branchNumeralElim 5 0 tag _ _ out xs ht ho
  have h1 := branchNumeralElim 5 1 tag _ _ out xs ht h0
  have h2 := branchNumeralElim 5 2 tag _ _ out xs ht h1
  have h3 := branchNumeralElim 5 3 tag _ _ out xs ht h2
  have h4 := branchNumeralElim 5 4 tag _ _ out xs ht h3
  have h5 := branchNumeralElim 5 5 tag _ _ out xs ht h4
  exact h5

theorem tag6Intro (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 6) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (OriginalRawSyntaxTransport.constant 3 1) out xs))) :
    Nonempty (Derivation body Delta (programGraph (choose n) out xs)) := by
  unfold choose
  apply branchNumeralIntro 6 0 tag _ _ out xs ht
  apply branchNumeralIntro 6 1 tag _ _ out xs ht
  apply branchNumeralIntro 6 2 tag _ _ out xs ht
  apply branchNumeralIntro 6 3 tag _ _ out xs ht
  apply branchNumeralIntro 6 4 tag _ _ out xs ht
  apply branchNumeralIntro 6 5 tag _ _ out xs ht
  apply branchNumeralIntro 6 6 tag _ _ out xs ht
  exact ho

theorem tag6Elim (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 6) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (choose n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (OriginalRawSyntaxTransport.constant 3 1) out xs)) := by
  have h0 := branchNumeralElim 6 0 tag _ _ out xs ht ho
  have h1 := branchNumeralElim 6 1 tag _ _ out xs ht h0
  have h2 := branchNumeralElim 6 2 tag _ _ out xs ht h1
  have h3 := branchNumeralElim 6 3 tag _ _ out xs ht h2
  have h4 := branchNumeralElim 6 4 tag _ _ out xs ht h3
  have h5 := branchNumeralElim 6 5 tag _ _ out xs ht h4
  have h6 := branchNumeralElim 6 6 tag _ _ out xs ht h5
  exact h6

theorem tag7Intro (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 7) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (binaryBranch) out xs))) :
    Nonempty (Derivation body Delta (programGraph (choose n) out xs)) := by
  unfold choose
  apply branchNumeralIntro 7 0 tag _ _ out xs ht
  apply branchNumeralIntro 7 1 tag _ _ out xs ht
  apply branchNumeralIntro 7 2 tag _ _ out xs ht
  apply branchNumeralIntro 7 3 tag _ _ out xs ht
  apply branchNumeralIntro 7 4 tag _ _ out xs ht
  apply branchNumeralIntro 7 5 tag _ _ out xs ht
  apply branchNumeralIntro 7 6 tag _ _ out xs ht
  apply branchNumeralIntro 7 7 tag _ _ out xs ht
  exact ho

theorem tag7Elim (n : Nat) (xs : Fin 3 → OTerm alpha) (out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph tag (numeral 7) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (choose n) out xs))) :
    Nonempty (Derivation body Delta (programGraph (binaryBranch) out xs)) := by
  have h0 := branchNumeralElim 7 0 tag _ _ out xs ht ho
  have h1 := branchNumeralElim 7 1 tag _ _ out xs ht h0
  have h2 := branchNumeralElim 7 2 tag _ _ out xs ht h1
  have h3 := branchNumeralElim 7 3 tag _ _ out xs ht h2
  have h4 := branchNumeralElim 7 4 tag _ _ out xs ht h3
  have h5 := branchNumeralElim 7 5 tag _ _ out xs ht h4
  have h6 := branchNumeralElim 7 6 tag _ _ out xs ht h5
  have h7 := branchNumeralElim 7 7 tag _ _ out xs ht h6
  exact h7
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseInternalProof
