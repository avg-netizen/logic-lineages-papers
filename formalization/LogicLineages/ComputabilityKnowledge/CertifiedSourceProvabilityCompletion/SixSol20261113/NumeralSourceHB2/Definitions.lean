module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2
open GorbowSyntax GorbowPRProgram HistoryRuleSuffix
/-- Fixed extra carrier installs both ORIGINAL MP constructor and actual unary
numeral prefix AST. Its semantics is not used as a correctness premise. -/
def carrier : Program 4 := applyTwo (.projection 0 : Program 2)
 LiteralRawMP.constructor (applyOne LiteralNumeralPrefix.numeralCode (.projection 0))
def scanClause (ntag stag ptag ctag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure (.equal
  (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag (.var 1 : Term 3)) (.var 2))
   (LiteralNumeralPrefix.numeralCall ntag (.var 0))) (.succ (.var 2)))
def continuationClause (ntag stag ptag ctag atag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure (.equal
  (LiteralSyntaxScan.scanCall stag
   (HistoryLookup.consCall ctag (LiteralNumeralPrefix.termTask ptag (.var 1 : Term 4)) (.var 2))
   (HistoryAppend.appendCall atag (LiteralNumeralPrefix.numeralCall ntag (.var 0)) (.var 3)))
  (LiteralSyntaxScan.scanCall stag (.var 2) (.var 3)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2
