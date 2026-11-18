module
public import LogicLineages.OrdinalComparison.OneNameSourceBooleanDefinitions
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyOneName
open OrdinalComparison Source Source.ForwardTranslation
noncomputable def actualOneNameSourceAtom (p : AdmissibleSum.Policy) {τ υ : Ty} (relation : OneInputOrderRelation)
    (a : OriginalTerm [Ty.ground] τ) (b : OriginalTerm [Ty.ground] υ) (x : Nat) : Prop :=
  ∃ (av : OrdinalVector [Ty.ground] τ.level) (bv : OrdinalVector [Ty.ground] υ.level),
    AdmissibleAssignment.assignment p a=some av ∧
    AdmissibleAssignment.assignment p b=some bv ∧
    match relation with
    | .equal => GroundSourceEquality.SourceEqualityAt av bv (fun _ => x)
    | .weak => SourceComparisonAt false av bv (fun _ => x)
    | .strict => SourceComparisonAt true av bv (fun _ => x)

noncomputable def actualOneNameSourceBooleanValue (p : AdmissibleSum.Policy) : OneNameSourceBooleanExpr → Nat → Bool
  | .truth value, _ => value
  | .atom relation a b, x => @decide (actualOneNameSourceAtom p relation a b x) (Classical.propDecidable _)
  | .neg formula, x => !(actualOneNameSourceBooleanValue p formula x)
  | .conj left right, x => actualOneNameSourceBooleanValue p left x && actualOneNameSourceBooleanValue p right x
  | .disj left right, x => actualOneNameSourceBooleanValue p left x || actualOneNameSourceBooleanValue p right x

def encodedOneNameSourceGuard (relation : Nat) (q : EncodedQuery) : Bool :=
  if relation=0 then positiveComparison q.2.1.2 q.2.2.2 && positiveComparison q.2.2.2 q.2.1.2
  else positiveComparison q.2.1.2 q.2.2.2

/-- Compute the original fixed-policy assignment, exact syntax normalization and
closed positive-coordinate guards BEFORE forming the positive scalar atom. -/
noncomputable def encodedOneNameSourceAtomProgram (p : AdmissibleSum.Policy) (relation n m : Nat) : List OneInputBooleanInstruction :=
  match PolicySourceEquality.compileSyntax p 1 n m with
  | none => [(0,0,0)]
  | some syn =>
    let q := normalizeQuerySyntaxCode syn
    [(if encodedOneNameSourceGuard relation q then 1 else 0,0,0),
      (2+relation,q.2.1.1,q.2.2.1),(6,0,0)]

noncomputable def encodedOneNameSourceBooleanProgram (p : AdmissibleSum.Policy) (program : List OneInputBooleanInstruction) : List OneInputBooleanInstruction :=
  program.flatMap (fun instruction =>
    if 2 ≤ instruction.1 ∧ instruction.1 ≤ 4 then
      encodedOneNameSourceAtomProgram p (instruction.1-2) instruction.2.1 instruction.2.2
    else [instruction])

noncomputable def encodedOneNameSourceBooleanValue (p : AdmissibleSum.Policy) (program : List OneInputBooleanInstruction) (x : Nat) : Bool :=
  encodedOneInputBooleanValue (encodedOneNameSourceBooleanProgram p program) x

noncomputable def encodedOneNameSourceBooleanClosures (p : AdmissibleSum.Policy) (program : List OneInputBooleanInstruction) : Bool × Bool :=
  encodedOneInputBooleanClosures (encodedOneNameSourceBooleanProgram p program)


/-- Independent literal zero-padded original-admissible vector semantics. -/
noncomputable def originalAtom (p : AdmissibleSum.Policy) {τ υ : Ty}
    (relation : OneInputOrderRelation) (a : OriginalTerm [Ty.ground] τ)
    (b : OriginalTerm [Ty.ground] υ) (s : OriginalDomain.AdmissibleSubstitution [Ty.ground]) : Prop :=
  ∃ (av : OrdinalVector [Ty.ground] τ.level) (bv : OrdinalVector [Ty.ground] υ.level),
    AdmissibleAssignment.assignment p a=some av ∧ AdmissibleAssignment.assignment p b=some bv ∧
    match relation with
    | .equal => ∀ j, PolicySourceEquality.vectorAt av s j=PolicySourceEquality.vectorAt bv s j
    | .weak => ∀ j, PolicySourceEquality.vectorAt av s j≤PolicySourceEquality.vectorAt bv s j
    | .strict => PolicySourceEquality.vectorAt av s 0<PolicySourceEquality.vectorAt bv s 0 ∧
      ∀ j, PolicySourceEquality.vectorAt av s (j+1)≤PolicySourceEquality.vectorAt bv s (j+1)

noncomputable def originalValue (p : AdmissibleSum.Policy) : OneNameSourceBooleanExpr →
    OriginalDomain.AdmissibleSubstitution [Ty.ground] → Bool
  | .truth b, _ => b
  | .atom r a b, s => @decide (originalAtom p r a b s) (Classical.propDecidable _)
  | .neg a, s => !(originalValue p a s)
  | .conj a b, s => originalValue p a s && originalValue p b s
  | .disj a b, s => originalValue p a s || originalValue p b s
end LogicLineages.StandardControlCurrent.PolicyOneName
