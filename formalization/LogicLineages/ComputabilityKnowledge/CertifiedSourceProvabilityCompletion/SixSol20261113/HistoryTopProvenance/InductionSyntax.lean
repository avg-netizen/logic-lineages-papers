module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionSyntax
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open Induction SyntaxProof

theorem substAllFuel {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag (count lines context raw tail remaining index : Term m) :
 substituteFormula sub (allFuel itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index) =
 allFuel itag ptag ctag vtag leftTag rightTag (substitute sub count) (substitute sub lines) (substitute sub context) (substitute sub raw) (substitute sub tail) (substitute sub remaining) (substitute sub index) := by
 simp only [allFuel,substituteFormula,substProvenance,HistoryOrder.SupportProof.substituteLift,
   substitute,liftSubstitute,Fin.cases_zero]

theorem allFuelAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw tail remaining index fuel : Term ctx) :
 GorbowStandardInstances.instantiate
   (provenance itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (.var 0)) fuel =
 provenance itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index fuel := by
 simp only [GorbowStandardInstances.instantiate,substProvenance,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem substAllIndex {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag (count lines context raw tail remaining : Term m) :
 substituteFormula sub (allIndex itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining) =
 allIndex itag ptag ctag vtag leftTag rightTag (substitute sub count) (substitute sub lines) (substitute sub context) (substitute sub raw) (substitute sub tail) (substitute sub remaining) := by
 simp only [allIndex,substituteFormula,substAllFuel,HistoryOrder.SupportProof.substituteLift,
   substitute,liftSubstitute,Fin.cases_zero]

theorem allIndexAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw tail remaining index : Term ctx) :
 GorbowStandardInstances.instantiate
   (allFuel itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (.var 0)) index =
 allFuel itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining index := by
 simp only [GorbowStandardInstances.instantiate,substAllFuel,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem substAllRemaining {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag (count lines context raw tail : Term m) :
 substituteFormula sub (allRemaining itag ptag ctag vtag leftTag rightTag count lines context raw tail) =
 allRemaining itag ptag ctag vtag leftTag rightTag (substitute sub count) (substitute sub lines) (substitute sub context) (substitute sub raw) (substitute sub tail) := by
 simp only [allRemaining,substituteFormula,substAllIndex,HistoryOrder.SupportProof.substituteLift,
   substitute,liftSubstitute,Fin.cases_zero]

theorem allRemainingAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw tail remaining : Term ctx) :
 GorbowStandardInstances.instantiate
   (allIndex itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (.var 0)) remaining =
 allIndex itag ptag ctag vtag leftTag rightTag count lines context raw tail remaining := by
 simp only [GorbowStandardInstances.instantiate,substAllIndex,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem substAllTail {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag (count lines context raw : Term m) :
 substituteFormula sub (allTail itag ptag ctag vtag leftTag rightTag count lines context raw) =
 allTail itag ptag ctag vtag leftTag rightTag (substitute sub count) (substitute sub lines) (substitute sub context) (substitute sub raw) := by
 simp only [allTail,substituteFormula,substAllRemaining,HistoryOrder.SupportProof.substituteLift,
   substitute,liftSubstitute,Fin.cases_zero]

theorem allTailAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw tail : Term ctx) :
 GorbowStandardInstances.instantiate
   (allRemaining itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (.var 0)) tail =
 allRemaining itag ptag ctag vtag leftTag rightTag count lines context raw tail := by
 simp only [GorbowStandardInstances.instantiate,substAllRemaining,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem substAllRaw {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag (count lines context : Term m) :
 substituteFormula sub (allRaw itag ptag ctag vtag leftTag rightTag count lines context) =
 allRaw itag ptag ctag vtag leftTag rightTag (substitute sub count) (substitute sub lines) (substitute sub context) := by
 simp only [allRaw,substituteFormula,substAllTail,HistoryOrder.SupportProof.substituteLift,
   substitute,liftSubstitute,Fin.cases_zero]

theorem allRawAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context raw : Term ctx) :
 GorbowStandardInstances.instantiate
   (allTail itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (.var 0)) raw =
 allTail itag ptag ctag vtag leftTag rightTag count lines context raw := by
 simp only [GorbowStandardInstances.instantiate,substAllTail,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem substAllContext {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag (count lines : Term m) :
 substituteFormula sub (allContext itag ptag ctag vtag leftTag rightTag count lines) =
 allContext itag ptag ctag vtag leftTag rightTag (substitute sub count) (substitute sub lines) := by
 simp only [allContext,substituteFormula,substAllRaw,HistoryOrder.SupportProof.substituteLift,
   substitute,liftSubstitute,Fin.cases_zero]

theorem allContextAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines context : Term ctx) :
 GorbowStandardInstances.instantiate
   (allRaw itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (.var 0)) context =
 allRaw itag ptag ctag vtag leftTag rightTag count lines context := by
 simp only [GorbowStandardInstances.instantiate,substAllRaw,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem substAllLines {m n : Nat} (sub : Fin m → Term n) itag ptag ctag vtag leftTag rightTag (count : Term m) :
 substituteFormula sub (allLines itag ptag ctag vtag leftTag rightTag count) =
 allLines itag ptag ctag vtag leftTag rightTag (substitute sub count) := by
 simp only [allLines,substituteFormula,substAllContext,HistoryOrder.SupportProof.substituteLift,
   substitute,liftSubstitute,Fin.cases_zero]

theorem allLinesAt {ctx : Nat} itag ptag ctag vtag leftTag rightTag (count lines : Term ctx) :
 GorbowStandardInstances.instantiate
   (allContext itag ptag ctag vtag leftTag rightTag (liftTerm count) (.var 0)) lines =
 allContext itag ptag ctag vtag leftTag rightTag count lines := by
 simp only [GorbowStandardInstances.instantiate,substAllContext,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.InductionSyntax
