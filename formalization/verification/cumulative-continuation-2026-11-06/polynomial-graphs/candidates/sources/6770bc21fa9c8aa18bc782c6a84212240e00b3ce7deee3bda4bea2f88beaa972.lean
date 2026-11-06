module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets

def CallCompilationCorrect : Prop := ∀ (calls : List Call) (t : Nat),
  (∀ p ∈ calls, 1 ≤ p.1) → CallsGenuine calls t →
    UnaryDomain (compileCalls calls) t ∧
    unaryValue (compileCalls calls) t =
      2*((callRun calls t).1 + (callRun calls t).2 : Nat)

def CallCompilationDegree : Prop := ∀ (D : Nat) (calls : List Call), 3 ≤ D →
  (∀ p ∈ calls, 1 ≤ p.1 ∧ p.1 ≤ D) → UnaryAllowed D (compileCalls calls)

def PolynomialCalls : Prop := ∀ o : NONote, Order.IsSuccLimit o.1.repr →
  o.1.repr < Ordinal.omega0 ^ Ordinal.omega0 →
    ∀ p ∈ principalKernelWord (principalExponentBlocks o.1) 0,
      1 ≤ Vendor.R1.treeWeight p.1 ∧
      p.1 = ONote.ofNat (Vendor.R1.treeWeight p.1) ∧
      Vendor.R1.treeWeight p.1 ≤ Vendor.R1.treeWeight o.1

def HeadCodeCalibration : Prop := ∀ o : ONote,
  headCalls (rawNoteEncode o) =
    (principalKernelWord (principalExponentBlocks o) 0).map
      (fun p => (Vendor.R1.treeWeight p.1,p.2)) ∧
    headDegree (rawNoteEncode o) = 3+Vendor.R1.treeWeight o

def PolynomialHeadCoverage : Prop := ∀ lam : Ordinal.{0},
  Order.IsSuccLimit lam → lam < Ordinal.omega0 ^ Ordinal.omega0 →
    ∃ o : NONote, o.1.repr = lam ∧ ValidHead (rawNoteEncode o.1)

def HeadGraphExact : Prop := ∀ code : Nat, ValidHead code →
  UnaryAllowed (headDegree code) (headRow code) ∧
    ∀ n : Nat, UnaryDomain (headRow code) n ∧
      unaryValue (headRow code) n = 2*(headValue code n : Int)

def HeadGraphTotalFunctional : Prop := ∀ code : Nat, ValidHead code →
  graphCutoff code = 0 ∧ graphExceptions code = [] ∧
    (∀ n y : Nat, HeadGraph code n y ↔ y = headValue code n) ∧
    (∀ n : Nat, ∃! y : Nat, HeadGraph code n y)

def HeadEquationExact : Prop := ∀ code : Nat, ValidHead code →
  ∀ input output : Nat,
    RowAllowed (headDegree code) (headEquation code input output) ∧
    ∀ ν : Nat → Nat, RowDomain (headEquation code input output) ν ∧
      (RowValue (headEquation code input output) ν = 0 ↔
        ν output = headValue code (ν input))

def FiniteFamilyDegree : Prop := ∀ codes : List Nat,
  (∀ code ∈ codes, ValidHead code) →
    3 ≤ familyDegree codes ∧ ∀ code ∈ codes,
      UnaryAllowed (familyDegree codes) (headRow code)

def HeadPrograms : Prop := Primrec headCalls ∧ Primrec compileCalls ∧
  Primrec headRow ∧ Primrec headDegree ∧ Primrec familyDegree ∧
  Primrec (fun p : Nat × Nat × Nat => headEquation p.1 p.2.1 p.2.2)

def FullPolynomialHeadGraphs : Prop := PolynomialHeadCoverage ∧ HeadGraphExact ∧
  HeadGraphTotalFunctional ∧ HeadEquationExact ∧ FiniteFamilyDegree ∧ HeadPrograms

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
