module
public import LogicLineages.OrdinalComparison.OneInputBooleanDefinitions
public import LogicLineages.OrdinalComparison.GroundSourceEqualityDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison
open Source Source.ForwardTranslation

/-- Every atom uses the SAME singleton ground context, with unrestricted
original internal and output types. Zero-use of that name is allowed. -/
inductive OneNameSourceBooleanExpr where
  | truth (value : Bool)
  | atom {τ υ : Ty} (relation : OneInputOrderRelation)
      (left : OriginalTerm [Ty.ground] τ) (right : OriginalTerm [Ty.ground] υ)
  | neg (formula : OneNameSourceBooleanExpr)
  | conj (left right : OneNameSourceBooleanExpr)
  | disj (left right : OneNameSourceBooleanExpr)

noncomputable def actualOneNameSourceAtom {τ υ : Ty} (relation : OneInputOrderRelation)
    (a : OriginalTerm [Ty.ground] τ) (b : OriginalTerm [Ty.ground] υ) (x : Nat) : Prop :=
  ∃ (av : OrdinalVector [Ty.ground] τ.level) (bv : OrdinalVector [Ty.ground] υ.level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a=some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b=some bv ∧
    match relation with
    | .equal => GroundSourceEquality.SourceEqualityAt av bv (fun _ => x)
    | .weak => SourceComparisonAt false av bv (fun _ => x)
    | .strict => SourceComparisonAt true av bv (fun _ => x)

noncomputable def actualOneNameSourceBooleanValue : OneNameSourceBooleanExpr → Nat → Bool
  | .truth value, _ => value
  | .atom relation a b, x => @decide (actualOneNameSourceAtom relation a b x) (Classical.propDecidable _)
  | .neg formula, x => !(actualOneNameSourceBooleanValue formula x)
  | .conj left right, x => actualOneNameSourceBooleanValue left x && actualOneNameSourceBooleanValue right x
  | .disj left right, x => actualOneNameSourceBooleanValue left x || actualOneNameSourceBooleanValue right x

/-- Literal SOURCE syntax instructions, not precompiled scalar coordinates. -/
def oneNameSourceBooleanCompile : OneNameSourceBooleanExpr → List OneInputBooleanInstruction
  | .truth b => [(if b then 1 else 0,0,0)]
  | .atom relation a b => [(2+oneInputOrderRelationCode relation,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)]
  | .neg formula => oneNameSourceBooleanCompile formula++[(5,0,0)]
  | .conj left right => oneNameSourceBooleanCompile left++oneNameSourceBooleanCompile right++[(6,0,0)]
  | .disj left right => oneNameSourceBooleanCompile left++oneNameSourceBooleanCompile right++[(7,0,0)]

def encodedOneNameSourceGuard (relation : Nat) (q : EncodedQuery) : Bool :=
  if relation=0 then positiveComparison q.2.1.2 q.2.2.2 && positiveComparison q.2.2.2 q.2.1.2
  else positiveComparison q.2.1.2 q.2.2.2

/-- Compute the original default assignment, exact syntax normalization and
closed positive-coordinate guards BEFORE forming the positive scalar atom. -/
noncomputable def encodedOneNameSourceAtomProgram (relation n m : Nat) : List OneInputBooleanInstruction :=
  match OriginalInput.compileSyntax (1,false,n,m) with
  | none => [(0,0,0)]
  | some syn =>
    let q := normalizeQuerySyntaxCode syn
    [(if encodedOneNameSourceGuard relation q then 1 else 0,0,0),
      (2+relation,q.2.1.1,q.2.2.1),(6,0,0)]

noncomputable def encodedOneNameSourceBooleanProgram (program : List OneInputBooleanInstruction) : List OneInputBooleanInstruction :=
  program.flatMap (fun instruction =>
    if 2 ≤ instruction.1 ∧ instruction.1 ≤ 4 then
      encodedOneNameSourceAtomProgram (instruction.1-2) instruction.2.1 instruction.2.2
    else [instruction])

noncomputable def encodedOneNameSourceBooleanValue (program : List OneInputBooleanInstruction) (x : Nat) : Bool :=
  encodedOneInputBooleanValue (encodedOneNameSourceBooleanProgram program) x

noncomputable def encodedOneNameSourceBooleanClosures (program : List OneInputBooleanInstruction) : Bool × Bool :=
  encodedOneInputBooleanClosures (encodedOneNameSourceBooleanProgram program)

end LogicLineages.OrdinalComparison
