module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalLambdaTraversalInternalSubstitutionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Distinct finite numeral terms are separated by successor injectivity and
successor-not-zero inside the original arithmetic calculus. -/
def numeralNeApply (m n : Nat) (h : m ≠ n)
    (he : Derivation body Delta (eqn (numeral m : OTerm alpha) (numeral n))) :
    Derivation body Delta ⊥ := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact False.elim (h rfl)
    | succ n => exact zeroNeSuc he
  | succ m ih =>
    cases n with
    | zero => exact sucNeZeroApply he
    | succ n => exact ih n (fun e => h (congrArg Nat.succ e)) (cancelSuc he)

theorem numeralNe (m n : Nat) (h : m ≠ n) :
    Nonempty (Derivation body Delta (equal (numeral m : OTerm alpha) (numeral n)).not) := by
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  apply numeralNeApply m n h
  simpa only [equalEqn] using
    (Derivation.hypothesis List.mem_cons_self : Derivation body
      (equal (numeral m : OTerm alpha) (numeral n) :: Delta) (equal (numeral m) (numeral n)))

theorem sameReject {n : Nat} (p q : Program n) (x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (hn : Nonempty (Derivation body Delta (equal x y).not)) :
    Nonempty (Derivation body Delta (programGraph (sameOf p q) z xs)) := by
  apply InternalApplicationValidityStackAppendFrameQueryProof.equalityCases x y _
  · intro Theta inc he
    exact binaryValue InternalEqualityTest.equalityTest p q z x y xs he
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hp inc) (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hq inc)
  · intro Theta inc he
    obtain ⟨hne⟩ := InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hn inc
    obtain ⟨heq⟩ := InternalEqualityTestProof.equalityOfAcceptance x y he
    exact ⟨Derivation.explosion
      (Derivation.implicationElimination hne (by simpa only [equalEqn] using heq))⟩

theorem branchNumeralIntro {n : Nat} (tag expected : Nat) (p no yes : Program n)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph p (numeral tag) xs)))
    (ho : Nonempty (Derivation body Delta
      (programGraph (if tag = expected then yes else no) out xs))) :
    Nonempty (Derivation body Delta
      (programGraph (InternalAcceptance.branch (sameOf p (constant n expected)) no yes) out xs)) := by
  by_cases he : tag = expected
  · subst expected
    exact successorBranchIntro _ no yes out z xs
      (InternalApplicationStepPeelSupportProof.sameAccept p (constant n tag) (numeral tag) xs ht
        (constantValue tag xs)) (by simpa only [if_pos rfl,if_true] using ho)
  · exact zeroBranchIntro _ no yes out xs
      (sameReject p (constant n expected) (numeral tag) (numeral expected) xs ht
        (constantValue expected xs) (numeralNe tag expected he))
      (by simpa only [if_neg he] using ho)

theorem branchNumeralElim {n : Nat} (tag expected : Nat) (p no yes : Program n)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph p (numeral tag) xs)))
    (ho : Nonempty (Derivation body Delta
      (programGraph (InternalAcceptance.branch (sameOf p (constant n expected)) no yes) out xs))) :
    Nonempty (Derivation body Delta
      (programGraph (if tag = expected then yes else no) out xs)) := by
  by_cases he : tag = expected
  · subst expected
    simpa only [if_pos rfl,if_true] using successorBranchElim _ no yes out z xs
      (InternalApplicationStepPeelSupportProof.sameAccept p (constant n tag) (numeral tag) xs ht
        (constantValue tag xs)) ho
  · simpa only [if_neg he] using zeroBranchElim _ no yes out xs
      (sameReject p (constant n expected) (numeral tag) (numeral expected) xs ht
        (constantValue expected xs) (numeralNe tag expected he)) ho

theorem twoTuple {X : Type} (xs : Fin 2 → X) :
    Fin.cons (xs 0) (Fin.cons (xs 1) Fin.elim0) = xs := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

/-- The outer pairing graph alone determines its left component. -/
theorem pairOfLeft {n : Nat} (p q : Program n) (raw out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph (pairOf p q) raw xs)))
    (hp : Nonempty (Derivation body Delta (programGraph p out xs))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left out raw)) := by
  apply programCompositionCases InternalPairing.pairing ![p,q] raw xs _ hc
  intro beta j ys Theta hj hpair hs
  simp only [graph1Rename]
  have hp' := renameInto hp j Theta hj
  simp only [programRename] at hp'
  exact outputTransport InternalUnpair.left (ys 0) (out.relabel j)
    (Fin.cons (raw.relabel j) Fin.elim0)
    (valueUnique p (ys 0) (out.relabel j) (fun i => (xs i).relabel j) (hs 0) hp')
    (pairLeft (raw.relabel j) (ys 0) (ys 1) (by simpa only [graph2,twoTuple] using hpair))

/-- The right component is recovered without an externally supplied witness. -/
theorem pairOfRight {n : Nat} (p q : Program n) (raw out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph (pairOf p q) raw xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q out xs))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.right out raw)) := by
  apply programCompositionCases InternalPairing.pairing ![p,q] raw xs _ hc
  intro beta j ys Theta hj hpair hs
  simp only [graph1Rename]
  have hq' := renameInto hq j Theta hj
  simp only [programRename] at hq'
  exact outputTransport InternalUnpair.right (ys 1) (out.relabel j)
    (Fin.cons (raw.relabel j) Fin.elim0)
    (valueUnique q (ys 1) (out.relabel j) (fun i => (xs i).relabel j) (hs 1) hq')
    (pairRight (raw.relabel j) (ys 0) (ys 1) (by simpa only [graph2,twoTuple] using hpair))

/-- A proof-only syntactic path through literal pair constructor ASTs.
False selects left, true selects right; no arithmetic semantic oracle is used. -/
inductive PairPath {n : Nat} : Program n → List Bool → Program n → Prop
  | here (p : Program n) : PairPath p [] p
  | left {p q selected : Program n} {path : List Bool} (h : PairPath p path selected) :
      PairPath (pairOf p q) (false :: path) selected
  | right {p q selected : Program n} {path : List Bool} (h : PairPath q path selected) :
      PairPath (pairOf p q) (true :: path) selected

def pathQuery {n : Nat} : List Bool → Program n → Program n
  | [], p => p
  | false :: rest, p => pathQuery rest (leftOf p)
  | true :: rest, p => pathQuery rest (rightOf p)

/-- Every path law is proved from original pairing inverse graphs, totality,
composition and functionality, at arbitrary symbolic arguments and context. -/
theorem pathValue {m n : Nat} {constructor selected : Program m} {path : List Bool}
    (h : PairPath constructor path selected)
    (query : Program n) (raw out : OTerm alpha)
    (cs : Fin m → OTerm alpha) (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph constructor raw cs)))
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (hs : Nonempty (Derivation body Delta (programGraph selected out cs))) :
    Nonempty (Derivation body Delta (programGraph (pathQuery path query) out xs)) := by
  induction h generalizing alpha query with
  | here p =>
    exact outputTransport query raw out xs (valueUnique p raw out cs hc hs) hq
  | @left p q selected path h ih =>
    apply programCases p cs _
    intro beta j Theta v hj hv
    simp only [programRename]
    have hc' := renameInto hc j Theta hj
    have hq' := renameInto hq j Theta hj
    have hs' := renameInto hs j Theta hj
    simp only [programRename] at hc' hq' hs'
    exact ih (leftOf query) v (out.relabel j)
      (fun i => (cs i).relabel j) (fun i => (xs i).relabel j) hv
      (unaryValue InternalUnpair.left query v (raw.relabel j) (fun i => (xs i).relabel j)
        (pairOfLeft p q (raw.relabel j) v (fun i => (cs i).relabel j) hc' hv) hq') hs'
  | @right p q selected path h ih =>
    apply programCases q cs _
    intro beta j Theta v hj hv
    simp only [programRename]
    have hc' := renameInto hc j Theta hj
    have hq' := renameInto hq j Theta hj
    have hs' := renameInto hs j Theta hj
    simp only [programRename] at hc' hq' hs'
    exact ih (rightOf query) v (out.relabel j)
      (fun i => (cs i).relabel j) (fun i => (xs i).relabel j) hv
      (unaryValue InternalUnpair.right query v (raw.relabel j) (fun i => (xs i).relabel j)
        (pairOfRight p q (raw.relabel j) v (fun i => (cs i).relabel j) hc' hv) hq') hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
