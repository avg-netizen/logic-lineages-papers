import LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCode
import LogicLineages.PersistentMarking.NumberedWindowRawWitnessBits

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFrameView
open NumberedWindowSyntax
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode

def view : NTerm → Nat × List Nat
  | .free t x => (0,[encodeTy t,x])
  | .bound t i => (1,[encodeTy t,i])
  | .lam t q => (2,[encodeTy t,encodeTerm q])
  | .bottom t => (3,[encodeTy t])
  | .ordinary f bs => (4,[encodeHead f,encodeArgs bs])
  | .numbered f t k bs es => (5,[encodeHead f,encodeTy t,k,encodeArgs bs,encodeArgs es])
  | .auxApp s t q a => (6,[encodeTy s,encodeTy t,encodeTerm q,encodeTerm a])

end LogicLineages.PersistentMarking.NumberedWindowRawContextFrameView
