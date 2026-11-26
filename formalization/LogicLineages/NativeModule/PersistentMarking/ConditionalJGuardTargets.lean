module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJNilCarrierTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

/-! A guarded direct-replacement checker (Opus B, round 6; not a twin).

**These statements concern a different program from the original witness.** The original
direct-replacement checker `d` of the presentation is an opaque existence witness
(`NumberedWindowDirectProgramChecks.exact_DirectCertificateProgram`). Here
`guardedDirect d := branch (projection 0) (constantZero 3) d` is explicit code around it: it returns
0 when the source code is 0 and runs `d` otherwise. Because the original algorithm rejects every
step out of the empty code, the guarded program computes the same function, so it satisfies the
same `Evaluates` calibration for the window's original checks (`GuardEvaluates`). The presentation
`data i j r (guardedDirect d)` is therefore exactly as admissible as `data i j r d` for the uniform
internal hypothesis, which only asks for some programs evaluating the checks. On the guarded
presentation, `NilNoStep` is derivable in the calculus (`GuardNilNoStep`), and the J-singleton and
J-members components re-close without it. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJGuardTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowArithmeticScalarTargets (fixed)
open ConditionalJUnionTargets ConditionalJSingletonTargets

/-- Explicit guard: 0 at source code 0, the given checker otherwise. -/
def guardedDirect (d : Program 3) : Program 3 :=
  ID1Completion.InternalAcceptance.branch (.projection 0) (ID1Completion.InternalAcceptance.constantZero 3) d

/-- The guarded checker evaluates the same original direct check. -/
def GuardEvaluates : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (i j : Program 1) (r d : Program 3),
    Evaluates (checks S.entries (fixed S K)) i j r d →
    Evaluates (checks S.entries (fixed S K)) i j r (guardedDirect d)

/-- On the guarded presentation no replacement step leaves the empty code, inside the calculus. -/
def GuardNilNoStep : Prop :=
  ∀ (i j : Program 1) (r d : Program 3) (c : Nat), NilNoStep (data i j r (guardedDirect d)) c

def GuardedJSingleton : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (i j : Program 1) (r d : Program 3),
    Evaluates (checks S.entries (fixed S K)) i j r d →
    ∀ (c : Nat) (u : Program 2) (sg : Program 1),
      CarrierUnion (data i j r (guardedDirect d)) c u → MultisetSplit (data i j r (guardedDirect d)) c u →
      SingletonCarrier (data i j r (guardedDirect d)) c sg →
      DescendantGeneration (data i j r (guardedDirect d)) c u sg →
      SingletonAccessibility (data i j r (guardedDirect d)) c sg

def GuardedJMembers : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (i j : Program 1) (r d : Program 3),
    Evaluates (checks S.entries (fixed S K)) i j r d →
    ∀ (c : Nat) (u mem : Program 2) (sg : Program 1),
      CarrierUnion (data i j r (guardedDirect d)) c u → MultisetSplit (data i j r (guardedDirect d)) c u →
      SingletonCarrier (data i j r (guardedDirect d)) c sg →
      DescendantGeneration (data i j r (guardedDirect d)) c u sg →
      MemberGeneration (data i j r (guardedDirect d)) c u mem sg →
      MembersAccessibility (data i j r (guardedDirect d)) c mem

end LogicLineages.PersistentMarking.ConditionalJGuardTargets
