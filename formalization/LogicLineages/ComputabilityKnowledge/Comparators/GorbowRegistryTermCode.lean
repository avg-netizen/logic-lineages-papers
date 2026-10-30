module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryTermCode
open GorbowSyntax GorbowRegistryTuple GorbowAtomicParameters
open LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCode

def PairCalibration : Prop := ∀ n (a b : Term n),
  pairRaw (GorbowTermPrefixCode.encode a) (GorbowTermPrefixCode.encode b)=
    GorbowTermPrefixCode.encode (pairTerm a b)

def TupleCalibration : Prop := ∀ n (args : List (Term n)),
  tupleRaw (args.map GorbowTermPrefixCode.encode)=GorbowTermPrefixCode.encode (tupleTerm args)

def HeaderCalibration : Prop := ∀ n arity tag (args : List (Term n)),
  headerRaw arity tag (args.map GorbowTermPrefixCode.encode)=
    GorbowTermPrefixCode.encode (headerTerm arity tag args)

def EvaluationCalibration : Prop := ∀ n (t : Term n),
  evaluationRaw (GorbowTermPrefixCode.encode t)=GorbowTermPrefixCode.encode (evaluationTerm t)

def GuardCalibration : Prop := ∀ n (t : Term n),
  arithmeticGuardRaw (GorbowTermPrefixCode.encode t)=
    GorbowFormulaPrefixCode.encode (GorbowSortedQuantifierTruth.arithmeticTermGuard t)

def ClosureCalibration : Prop := ∀ n (φ : Formula n),
  closeRaw n (GorbowFormulaPrefixCode.encode φ)=GorbowFormulaPrefixCode.encode (arithmeticClosure φ)

def UniformPrograms : Prop :=
  Primrec (fun p : List Nat × List Nat => pairRaw p.1 p.2) ∧
  Primrec tupleRaw ∧ Primrec (fun p : Nat × Nat × List (List Nat) => headerRaw p.1 p.2.1 p.2.2) ∧
  Primrec evaluationRaw ∧ Primrec arithmeticGuardRaw ∧
  Primrec (fun p : Nat × List Nat => closeRaw p.1 p.2)

def Target : Prop := PairCalibration ∧ TupleCalibration ∧ HeaderCalibration ∧ EvaluationCalibration ∧
  GuardCalibration ∧ ClosureCalibration ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryTermCode
