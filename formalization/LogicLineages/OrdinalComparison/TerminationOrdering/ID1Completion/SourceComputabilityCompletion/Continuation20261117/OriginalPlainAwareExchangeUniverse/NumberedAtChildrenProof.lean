module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedAtChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open Continuation20261115
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atChildren (n : Nat) (arity : Fin n → Nat)
    (left right k l f g tau upsilon base dest ts us extras otherExtras node first last typ gamma window context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![k,f,tau,base,ts,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![l,g,upsilon,dest,us,otherExtras])))
    (hfirst : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first base dest)))
    (hlast : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last extras otherExtras)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  have hpair := andLeft hedge
  have hlg := andLeft (andRight hedge)
  have hrg := andLeft (andRight (andRight hedge))
  have he := andRight (andRight (andRight hedge))
  have hw := andRight (andRight (andRight henv))
  have hr := (OriginalDecodedNumberedRecurrence.Proof.numberedRecurrence n arity body alpha Delta
    left right k l f g tau upsilon base dest ts us extras otherExtras node first last window symbols types
    hlc hrc hpair hfirst hlast hw).mp he
  have hm := andLeft (andRight hr)
  have hrc' : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![k,g,tau,dest,ts,otherExtras])) := by
    apply NumberedInputProof.inputs right ![l,g,upsilon,dest,us,otherExtras] _ hrc
    apply SixCoordinateProof.coordinate_relation
      (fun x y : OTerm alpha => Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn x y)))
    · exact andLeft hm
    · exact ⟨refl _⟩
    · exact andLeft (andRight hm)
    · exact ⟨refl _⟩
    · exact andRight (andRight hm)
    · exact ⟨refl _⟩
  exact NumberedCasesProof.preserved n arity left right k f g tau base dest ts extras otherExtras
    first last typ gamma window context symbols types hlc hrc' hlg hrg hfirst hlast henv ih ha hp
    (andRight (andRight hr))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedAtChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedAtChildrenProof
