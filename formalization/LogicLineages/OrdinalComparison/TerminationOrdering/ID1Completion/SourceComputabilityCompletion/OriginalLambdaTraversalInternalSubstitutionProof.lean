module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalApplicationCertificateConstructorsSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Pure syntax substitution through composition trees. The outer primitive
recursive operator is retained literally, including every recursion AST. -/
inductive Substitutes {m n : Nat} (gs : Fin n → Program m) : Program n → Program m → Prop
  | projection (i : Fin n) : Substitutes gs (.projection i) (gs i)
  | composition {k : Nat} (f : Program k) (ps : Fin k → Program n) (qs : Fin k → Program m)
      (h : ∀ i, Substitutes gs (ps i) (qs i)) :
      Substitutes gs (.composition f ps) (.composition f qs)

/-- An internal graph calculation, not reflection of numeric evaluation. -/
theorem substitutionGraph {m n : Nat} {gs : Fin n → Program m}
    {p : Program n} {q : Program m} (h : Substitutes gs p q)
    {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (xs : Fin n → OTerm alpha) (ys : Fin m → OTerm alpha) (out : OTerm alpha)
    (hg : ∀ i, Nonempty (Derivation positive Delta (programGraph (gs i) (xs i) ys))) :
    Nonempty (Derivation positive Delta (programGraph p out xs)) ↔
      Nonempty (Derivation positive Delta (programGraph q out ys)) := by
  induction h generalizing alpha with
  | projection i =>
    constructor
    · intro hp
      obtain ⟨he⟩ := valueUnique (.projection i) out (xs i) xs hp (projectionValue i xs)
      exact outputTransport (gs i) (xs i) out ys ⟨InternalTagArithmeticSupportProof.symm he⟩ (hg i)
    · intro hq
      obtain ⟨he⟩ := valueUnique (gs i) out (xs i) ys hq (hg i)
      exact outputTransport (.projection i) (xs i) out xs
        ⟨InternalTagArithmeticSupportProof.symm he⟩ (projectionValue i xs)
  | composition f ps qs h ih =>
    constructor
    · intro hp
      apply programCompositionCases f ps out xs _ hp
      intro beta j zs Theta hj hf hs
      rw [programRename]
      apply compositionValue f qs (out.relabel j) (fun a => (ys a).relabel j) zs hf
      intro i
      apply (ih i (fun a => (xs a).relabel j) (fun a => (ys a).relabel j) (zs i) _).mp (hs i)
      intro a
      simpa only [programRename] using renameInto (hg a) j Theta hj
    · intro hq
      apply programCompositionCases f qs out ys _ hq
      intro beta j zs Theta hj hf hs
      rw [programRename]
      apply compositionValue f ps (out.relabel j) (fun a => (xs a).relabel j) zs hf
      intro i
      apply (ih i (fun a => (xs a).relabel j) (fun a => (ys a).relabel j) (zs i) _).mpr (hs i)
      intro a
      simpa only [programRename] using renameInto (hg a) j Theta hj

theorem constantZeroSubstitution {m n : Nat} (gs : Fin n → Program m) :
    Substitutes gs (InternalAcceptance.constantZero n) (InternalAcceptance.constantZero m) :=
  .composition .zero Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)

theorem unarySubstitution {m n : Nat} {gs : Fin n → Program m}
    (f : Program 1) {p : Program n} {q : Program m} (h : Substitutes gs p q) :
    Substitutes gs (.composition f (fun _ : Fin 1 => p))
      (.composition f (fun _ : Fin 1 => q)) :=
  .composition f _ _ (fun _ => h)

theorem binarySubstitution {m n : Nat} {gs : Fin n → Program m}
    (f : Program 2) {p r : Program n} {q s : Program m}
    (hp : Substitutes gs p q) (hr : Substitutes gs r s) :
    Substitutes gs (.composition f ![p,r]) (.composition f ![q,s]) :=
  .composition f _ _ (fun i => Fin.cases hp (Fin.cases hr (fun j => Fin.elim0 j)) i)

theorem oneSubstitution {m n : Nat} (gs : Fin n → Program m) :
    Substitutes gs (InternalLessThan.constantOne n) (InternalLessThan.constantOne m) :=
  unarySubstitution .succ (constantZeroSubstitution gs)

theorem twoSubstitution {m n : Nat} (gs : Fin n → Program m) :
    Substitutes gs (two n) (two m) := unarySubstitution .succ (oneSubstitution gs)

theorem pairSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p r : Program n} {q s : Program m}
    (hp : Substitutes gs p q) (hr : Substitutes gs r s) :
    Substitutes gs (pairOf p r) (pairOf q s) := binarySubstitution _ hp hr

theorem consSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p r : Program n} {q s : Program m}
    (hp : Substitutes gs p q) (hr : Substitutes gs r s) :
    Substitutes gs (consOf p r) (consOf q s) := binarySubstitution _ hp hr

theorem liveSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p r : Program n} {q s : Program m}
    (hp : Substitutes gs p q) (hr : Substitutes gs r s) :
    Substitutes gs (OriginalLambdaTraversal.liveOf p r) (OriginalLambdaTraversal.liveOf q s) :=
  pairSubstitution (oneSubstitution gs) (pairSubstitution hp hr)

theorem visitSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p r : Program n} {q s : Program m}
    (hp : Substitutes gs p q) (hr : Substitutes gs r s) :
    Substitutes gs (OriginalLambdaTraversal.visitOf p r) (OriginalLambdaTraversal.visitOf q s) :=
  pairSubstitution (constantZeroSubstitution gs) (pairSubstitution hp hr)

theorem applicationReturnSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p r : Program n} {q s : Program m}
    (hp : Substitutes gs p q) (hr : Substitutes gs r s) :
    Substitutes gs (OriginalLambdaTraversal.applicationReturnOf p r)
      (OriginalLambdaTraversal.applicationReturnOf q s) :=
  pairSubstitution (oneSubstitution gs) (pairSubstitution hp hr)

theorem lambdaReturnSubstitution {m n : Nat} {gs : Fin n → Program m}
    {p r : Program n} {q s : Program m}
    (hp : Substitutes gs p q) (hr : Substitutes gs r s) :
    Substitutes gs (OriginalLambdaTraversal.lambdaReturnOf p r)
      (OriginalLambdaTraversal.lambdaReturnOf q s) :=
  pairSubstitution (twoSubstitution gs) (pairSubstitution hp hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
