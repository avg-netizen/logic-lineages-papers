module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericInductionMatrixSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open Continuation20261115 Induction
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalTagArithmeticSyntaxProof (eqnSubst eqnRelabel zSubst sucSubst)
open InternalStrongInduction InternalStrongInductionSyntaxProof
open Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof (implicationRename)

theorem atFuelSubst {beta : Type} (n : Nat) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtFuel n raw).subst (fun a => emb (ts a)) = AtFuel n (raw.subst ts) := by
  let m : Formula (alpha ⊕ Fin 11) :=
    Meaning.holds n (.var (.inr 5)) (.var (.inr 6)) (raw.relabel Sum.inl)
      (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10))
  let m' : Formula (beta ⊕ Fin 11) :=
    Meaning.holds n (.var (.inr 5)) (.var (.inr 6)) ((raw.subst ts).relabel Sum.inl)
      (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10))
  change (InternalClosedPrograms.allBlock (GenericInductionMatrixSyntaxProof.matrix
    InternalPairing.pairing (OriginalEnumerationRecursion.enumeration n) contains raw m)).subst
    (fun a => emb (ts a)) = InternalClosedPrograms.allBlock
      (GenericInductionMatrixSyntaxProof.matrix InternalPairing.pairing
        (OriginalEnumerationRecursion.enumeration n) contains (raw.subst ts) m')
  apply GenericInductionMatrixSyntaxProof.allSubst
  dsimp only [m, m']
  rw [MeaningSyntaxProof.meaningSubst]
  change Meaning.holds n (.var (.inr 5)) (.var (.inr 6))
    ((raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 11)).subst
      (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i : Fin 11 => .var (.inr i))))
    (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) = _
  rw [InternalRecursionGraphSyntaxProof.liftSubst]


@[simp] theorem atFuelRename {beta : Type} (n : Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (AtFuel n raw).relabel j = AtFuel n (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtFuel n raw).subst (fun a => emb (.var (j a))) = _
  rw [atFuelSubst]
  simp only [← termRelabelAsSubst]

theorem predicateInstantiate (n : Nat) (raw : OTerm alpha) : instantiate (predicate n : Formula (alpha ⊕ Fin 1)) (emb raw) = AtFuel n raw := by
  rw [predicate,instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,atFuelSubst]
  simp only [InternalTagArithmeticSyntaxProof.varBind]

theorem predicateLift (n : Nat) : lift (predicate n : Formula (alpha ⊕ Fin 1)) = predicate n := by
  unfold predicate lift
  rw [atFuelRename]
  rfl

attribute [local irreducible] AtFuel

@[simp] theorem belowFuelRename {beta : Type} (n : Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (BelowFuel n raw).relabel j = BelowFuel n (raw.relabel j) := by
  unfold BelowFuel
  rw [InternalStrongInductionSyntaxProof.belowRename]
  congr 1
  unfold predicate
  rw [atFuelRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionSyntaxProof
