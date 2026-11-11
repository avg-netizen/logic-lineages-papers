module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimum
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original packed class membership. Inputs are [seed,candidate,parameter].
There is no source-universe filter and no closed-window premise. The selected
compiler for this predicate does not yet expose structural primary coherence. -/
def classValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3) : Nat :=
  InternalOriginalUniformParameterLeaves.decodedValue n (fun ctx obj =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).any
      (fun q => ContextUniformPrimary.classNumberTest arity ctx.1.1 ctx.1.2 obj.1 q
        (v.get 1))).toNat) (v.get 0) (v.get 2)

def ClassTestCalibrated (n : Nat) (arity : Fin n → Nat) (P : Program 3) : Prop :=
  ∀ v : List.Vector Nat 3, evaluate P v = classValue n arity v

/-- Only the reflexive candidate is routed through the original transparent
packed target. Native equality with P on EVERY vector is a separate obligation. -/
def reflexiveClassTest (T : Program 2) (P : Program 3) : Program 3 :=
  InternalAcceptance.branch
    (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0]) P
    (.composition T ![.projection 0,.projection 2])

/-- Inputs [index,previous,seed,parameter]. Previous values below index are
retained. Otherwise EXACTLY ONE accepts the current candidate; a miss advances
to index+1, so the sentinel is the bound, never zero by convention. -/
def scanStep (Q : Program 3) : Program 4 :=
  InternalAcceptance.branch
    (.composition InternalLessThan.ltTest ![.projection 1,.projection 0])
    (InternalAcceptance.branch
      (.composition InternalEqualityTest.equalityTest
        ![.composition Q ![.projection 2,.projection 0,.projection 3],
          InternalLessThan.constantOne 4])
      (.composition .succ (fun _ : Fin 1 => .projection 0)) (.projection 0))
    (.projection 1)

/-- Literal bounded primitive recursion, inputs [bound,seed,parameter]. -/
def scan (Q : Program 3) : Program 3 :=
  .recursion (InternalAcceptance.constantZero 2) (scanStep Q)

/-- Target rejection returns zero. Target acceptance searches through seed,
including its explicit reflexive hit. Inputs remain [seed,parameter]. -/
def minimum (T : Program 2) (P : Program 3) : Program 2 :=
  InternalAcceptance.branch
    (.composition InternalEqualityTest.equalityTest ![T,InternalLessThan.constantOne 2])
    (InternalAcceptance.constantZero 2)
    (.composition (scan (reflexiveClassTest T P))
      ![.composition .succ (fun _ : Fin 1 => .projection 0),.projection 0,.projection 1])

def graph3 {alpha : Type} (Q : Program 3) (out x y z : OTerm alpha) : Formula alpha :=
  programGraph Q out (Fin.cons x (Fin.cons y (Fin.cons z Fin.elim0)))

/-- Arithmetic out <= bound, written as out < bound+1. -/
def atMost {alpha : Type} (out bound : OTerm alpha) : Formula alpha :=
  InternalLessThan.strictLess out (OrdinaryArithmetic.succTerm bound)

/-- Every generic scan graph has the actual bound, first hit and absence of
any earlier hit. The last clause explicitly covers the exact-bound sentinel.
All conclusions concern internal graphs, never native evaluated predicates. -/
def ScanLaw (Q : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out bound seed parameter earlier : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph3 (scan Q) out bound seed parameter).imp
      (atMost out bound ⊓
        (((InternalLessThan.strictLess out bound).imp
          (graph3 Q InternalOriginalStepGuard.one seed out parameter)) ⊓
        (((InternalLessThan.strictLess earlier out).imp
          (graph3 Q InternalOriginalStepGuard.one seed earlier parameter).not) ⊓
        (((equal out bound) ⊓ InternalLessThan.strictLess earlier bound).imp
          (graph3 Q InternalOriginalStepGuard.one seed earlier parameter).not))))))

/-- The explicitly exposed reflexive branch, independent of native calibration. -/
def ReflexiveLaw (T : Program 2) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 T InternalOriginalStepGuard.one seed parameter).imp
      (graph3 (reflexiveClassTest T P) InternalOriginalStepGuard.one seed seed parameter)))

/-- Preguard least-hit law. This does not assert minimality after a rank
fallback, which can internally return the seed. -/
def MinimumLaw (T : Program 2) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out seed parameter earlier : OTerm alpha),
  Nonempty (Derivation body Delta
    (((graph2 T InternalOriginalStepGuard.one seed parameter) ⊓
      graph2 (minimum T P) out seed parameter).imp
      (atMost out seed ⊓
        ((graph3 (reflexiveClassTest T P) InternalOriginalStepGuard.one seed out parameter) ⊓
          ((InternalLessThan.strictLess earlier out).imp
            (graph3 (reflexiveClassTest T P) InternalOriginalStepGuard.one seed earlier parameter).not)))))

/-- Change ONLY the initial representative, before the accepted rank guard. -/
def minimumInputs (H G : Program 1) (P : Program 3)
    (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := { p.base with oldRepresentative := minimum (OriginalTypedDecoder.target H G) P } }

/-- Exactly one accepted rank guard, then the unchanged transparent leaves.
The later pipeline is refineInputs G q followed by the existing finalData. -/
def transparentInputs (H G : Program 1) (W : Program 2) (P : Program 3)
    (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  OriginalRankGuardedRepresentative.transparentInputs H G W (minimumInputs H G P p)

def LiteralFields (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let s := minimumInputs H G P p
  let q := transparentInputs H G W P p
  s.base.oldSource = p.base.oldSource ∧ s.base.oldTarget = p.base.oldTarget ∧
  s.base.member = p.base.member ∧ s.window = p.window ∧ s.oldSrc = p.oldSrc ∧
  s.oldComp = p.oldComp ∧ s.oldStep = p.oldStep ∧ s.oldVertex = p.oldVertex ∧
  s.oldResult = p.oldResult ∧
  s.base.oldRepresentative = minimum (OriginalTypedDecoder.target H G) P ∧
  q = OriginalRankGuardedRepresentative.transparentInputs H G W s

def NativePreparation (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (P : Program 3) : Prop :=
  (∀ v : List.Vector Nat 2,
    evaluate (minimumInputs H G P p).base.oldRepresentative v =
      evaluate p.base.oldRepresentative v) ∧
  GlobalSourcePackage.InputsCalibrated n arity (minimumInputs H G P p)

/-- Only class membership survives the rank guard: retain the minimum or
return the explicitly admitted reflexive seed. No postguard minimum claim. -/
def GuardedClassLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out seed parameter : OTerm alpha),
  let q := transparentInputs H G W P p
  Nonempty (Derivation body Delta
    (((graph2 (OriginalTypedDecoder.target H G) InternalOriginalStepGuard.one seed parameter) ⊓
      graph2 q.base.oldRepresentative out seed parameter).imp
      (graph3 (reflexiveClassTest (OriginalTypedDecoder.target H G) P)
        InternalOriginalStepGuard.one seed out parameter)))

/-- FULL accepted rank-guard Properties, and hence its complete inherited
Package, are reconstructed at precisely pMin, without selecting a new tuple. -/
def Retained (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  OriginalRankGuardedRepresentative.Properties n arity (minimumInputs H G P p) H G W

/-- Both original and pMin Properties coexist with all independent minimum
laws. Structural primary/exchange coherence and internal I/C remain pending. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  OriginalRankGuardedRepresentative.Properties n arity p H G W ∧
  ClassTestCalibrated n arity P ∧ LiteralFields p H G W P ∧
  NativePreparation n arity p H G P ∧
  ReflexiveLaw (OriginalTypedDecoder.target H G) P ∧
  ScanLaw (reflexiveClassTest (OriginalTypedDecoder.target H G) P) ∧
  MinimumLaw (OriginalTypedDecoder.target H G) P ∧
  GuardedClassLaw p H G W P ∧ Retained n arity p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimum
