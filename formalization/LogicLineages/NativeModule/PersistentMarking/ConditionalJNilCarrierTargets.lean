module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJSingletonTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperBridgeTargets

/-! The premise `NilCarrier` of #1489 for the actual Paper 16 presentation (Opus B, round 6;
not a twin): at any checker programs evaluating the window's original checks, the empty multiset
code is a J-carrier code, derivably in the calculus.  It is a closed instance, so it follows from
the accepted numeral evaluation of the (otherwise opaque) multiset-domain program; and the
re-closed `ConditionalJSingleton` / `ConditionalJMembers` for those programs without it. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJNilCarrierTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowArithmeticScalarTargets (fixed)
open ConditionalJUnionTargets ConditionalJSingletonTargets

def ActualNilCarrier : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (i j : Program 1) (r d : Program 3),
    Evaluates (checks S.entries (fixed S K)) i j r d → ∀ c, NilCarrier (data i j r d) c

def ActualJSingleton : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (i j : Program 1) (r d : Program 3),
    Evaluates (checks S.entries (fixed S K)) i j r d →
    ∀ (c : Nat) (u : Program 2) (sg : Program 1),
      CarrierUnion (data i j r d) c u → MultisetSplit (data i j r d) c u →
      SingletonCarrier (data i j r d) c sg → NilNoStep (data i j r d) c →
      DescendantGeneration (data i j r d) c u sg → SingletonAccessibility (data i j r d) c sg

def ActualJMembers : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (i j : Program 1) (r d : Program 3),
    Evaluates (checks S.entries (fixed S K)) i j r d →
    ∀ (c : Nat) (u mem : Program 2) (sg : Program 1),
      CarrierUnion (data i j r d) c u → MultisetSplit (data i j r d) c u →
      SingletonCarrier (data i j r d) c sg → NilNoStep (data i j r d) c →
      DescendantGeneration (data i j r d) c u sg → MemberGeneration (data i j r d) c u mem sg →
      MembersAccessibility (data i j r d) c mem

end LogicLineages.PersistentMarking.ConditionalJNilCarrierTargets
