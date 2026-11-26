module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.WindowProof
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

open ProgramRangeProof
open OriginalHeadWindow
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem typeRange (p : Program 3) : Ranged (typeMember p) :=
  compositionRange contains ![.projection 2,p] ProgramRangeProof.containsRange

theorem branchWindowRange (n : Nat) (arity : Fin n → Nat) (tag : Nat) :
    Ranged (branchWindow n arity tag) := by
  unfold branchWindow
  split
  · exact conjunctionRange _ _
  · split
    · exact conjunctionRange _ _
    · exact typeRange _

theorem payloadRange (n : Nat) (arity : Fin n → Nat) (tag : Nat) :
    Ranged (atPayload n arity tag) :=
  compositionRange _ _ (branchWindowRange n arity tag)

theorem chooseRange (tag : Nat) (yes no : Program 3) (hy : Ranged yes) (hn : Ranged no) :
    Ranged (choose tag yes no) := branchRange _ _ _ hn hy

theorem windowRanged (n : Nat) (arity : Fin n → Nat) : Ranged (window n arity) :=
  chooseRange 0 _ _ (payloadRange n arity 0)
    (chooseRange 1 _ _ (payloadRange n arity 1)
      (chooseRange 2 _ _ (payloadRange n arity 2)
        (chooseRange 3 _ _ (payloadRange n arity 3)
          (chooseRange 4 _ _ (payloadRange n arity 4)
            (chooseRange 5 _ _ (payloadRange n arity 5) (constantRange 3 0))))))

theorem windowRange : Targets.InternalWindowRange := by
  intro n arity body alpha Delta raw symbols types out h
  exact windowRanged n arity body alpha Delta out
    (Fin.cons raw (Fin.cons symbols (Fin.cons types Fin.elim0))) h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.WindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.WindowProof
