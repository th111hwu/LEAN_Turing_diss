import Lean
--#eval Lean.versionString

def extendBoolTape (t : Array Bool) : Array Bool :=
  t ++ [false]

def flipTape (n : Nat) (t : Array Bool) (newT : Array Bool) : Array Bool :=
  match n with
  | 0 => newT
  | n+1 => flipTape n t (newT ++ [t[n]])

--syntactic sugar since this are almost always the parameters for flipTape
def flipTapeShort (t : Array Bool) : Array Bool :=
  flipTape t.size t #[]

--k is the rewrite position, newT is the new tape, s is the new value to write and n is tape size
def rewriteHelp (k : Nat) (newT : Array Bool) (s : Bool) (t : Array Bool)  (n : Nat) : Array Bool :=
  match n, k with
  | 0, _ => newT
  | n+1, 0 => rewriteHelp (n+1) (newT ++ [s]) s t n
  | n+1, k+1 => rewriteHelp k (newT ++ [t[n]]) s t n

--s if the new value to be written at spot n in the tape, t is the tape
def rewrite (s : Bool) (t : Array Bool) (n : Nat) : Array Bool :=
  if s = t[n] then t --if they are the same don't do anything, saves computation
  else t.set! n s

def extendBoolTapeLeft (t : Array Bool) : Array Bool :=
  t.insertAt 0 false

structure TM where
  h : Nat
  t : Array Bool
  q : Int
deriving Repr

def makeTM (head : Nat) (tape : Array Bool) (qState : Int) : TM :=
  {h := head, t := tape, q := qState}

structure TMstate where
  q : Int
  s : Bool
  m : Int
deriving Repr

def makeTMstate (qState : Int) (symbol : Bool) (move : Int) : TMstate :=
  {q := qState, s := symbol, m := move}

--#eval makeTMstate 1 true 1

def translateMove (m : Int) (h : Nat) : Nat :=
  match m with
  | 1 => (h+1)
  | -1 => (h-1)
  | _ => h

def checkTapeBorders (t : Array Bool) (h : Nat) : TM :=
  match h, (t.size - h) with
  | 0, _ => makeTM (h+1) (extendBoolTapeLeft t) (-2)
  | _, 1 => makeTM h (extendBoolTape t) (-2)
  | _, _ => makeTM h t (-2)

def stepMoveHelp (tm : TM) (m : Int) : TM :=
  makeTM (translateMove m tm.h) tm.t (-2)

def stepMove (t : Array Bool) (h : Nat) (m : Int) : TM :=
  stepMoveHelp (checkTapeBorders t h) m

def copyTM (tm : TM) : TM :=
  {h := tm.h, t := tm.t, q := tm.q}

--this temp strat assumes that LEAN doesn't use pointers and instead actually stores a copy
--of the data at the "variable" location
--without a doubt the uglieast part of my code, since new variables cannot be created we must create
--one by passing a duplicate of the original inside since we need to fetch information from the old
--TM state while having one for which we can update the values
def inputStep (tm : TM) (tempTm : TM) (TMIcode : (h : Nat) → (t : Array Bool) → (q : Int) → TMstate) : TM :=
  makeTM (stepMove tm.t tm.h (TMIcode tm.h tm.t tm.q).m).h (rewrite (TMIcode tempTm.h tm.t tempTm.q).s (stepMove tm.t tempTm.h (TMIcode tempTm.h tm.t tm.q).m).t tempTm.h) (TMIcode tempTm.h tempTm.t tempTm.q).q
--can i just nest this massive set of calls in smaller functions and remove the temp faff?

def run (n : Nat) (tm : TM) (TMIcode : (h : Nat) → (t : Array Bool) → (q : Int) → TMstate) :=
  match n, tm.q with
  | 0, _ => tm
  | _, -1 => tm
  | n+1, _ => run n (inputStep tm (copyTM tm) TMIcode) TMIcode

--this function just exists to make interfacing with the tm slicker, just input max steps, tape and code
def interface (maxSteps : Nat) (tape : Array Bool) (TMIcode : (h : Nat) → (t : Array Bool) → (q : Int) → TMstate) :=
  (run maxSteps (makeTM 1 tape 0) TMIcode).t

def verifySegment (turingSeg : Bool) (verifierSeg : Bool) (validThusFar : Bool) : Bool :=
  (turingSeg ↔ verifierSeg) ∧ validThusFar
  --match turingSeg, verifierSeg, validThusFar with
  --| true, true, true => true
  --| false, false, true => true
  --| true, false, true => false
  --| false, true, true => false
  --| _, _, false => false

def trimOneEnd (t : Array Bool) (size : Nat) : Array Bool :=
  match size, t[size] with
  | 0, _ => t
  | n+1, false => trimOneEnd (t.eraseIdx (n+1)) (n)
  | n+1, true => t

def trimTapeHelp (t : Array Bool) : Array Bool :=
  trimOneEnd (flipTape t.size t #[]) (t.size-1)

def trimTape (t : Array Bool) : Array Bool :=
  flipTapeShort (trimTapeHelp (trimOneEnd t (t.size-1)))

def testPls := #[false, false, true, true, false, true, false]

--#eval trimTape testPls

def verifyTape (turingTape : Array Bool) (verifierTape : Array Bool) : Bool :=
  trimTape turingTape = trimTape verifierTape
  --match n with
  --| 0 => verifySegment turingTape[0] verifierTape[0] validThusFar --since the leftmost should always be false item zero need not be checked
  --| n+1 => verifyTape n turingTape verifierTape (verifySegment turingTape[n] verifierTape[n] validThusFar)


def tapeToIntHelp (n : Nat) (t : Array Bool) : Nat :=
  match n, t[n] with
  | 0, _ => 0
  | n+1, true => tapeToIntHelp n t + 1
  | n+1, false => tapeToIntHelp n t

def tapeToInt (t : Array Bool) : Nat :=
  tapeToIntHelp (t.size -1) t

def intToTapeHelp (n : Nat) : Array Bool :=
  match n with
  | 0 => #[false]
  | n+1 => (intToTapeHelp n) ++ #[true]

def intToTape (n : Nat) : Array Bool :=
  intToTapeHelp n ++ #[false]

def intToLTapeHelp (n : Nat) : List Bool :=
  match n with
  | 0 => [false]
  | n+1 => true :: (intToLTapeHelp n)

def intToLTape (n : Nat) : List Bool :=
  false :: intToLTapeHelp n

--succ n turing machine
def TMsucc (h : Nat) (t : Array Bool) (q : Int) : TMstate :=
  match t[h], q with
  | true, 0 => makeTMstate 0 true 1
  | false, 0 => makeTMstate (-1) true 1
  | _, _ => makeTMstate (-1) false 0

--addition turing machine
def TMadd (h : Nat) (t : Array Bool) (q : Int) : TMstate :=
  match t[h], q with
  | true, 0 => makeTMstate 0 true 1
  | false, 0 => makeTMstate 1 true 1
  | true, 1 => makeTMstate 1 true 1
  | false, 1 => makeTMstate 2 false (-1)
  | true, 2 => makeTMstate (-1) false 0
  | false, 2 => makeTMstate (-1) false 0 --error
  | _, _ => makeTMstate (-1) false 0

--#eval verifyTape 5 #[false, true, true, false, false] #[false, true, true, false, false] true

def threeTape : Array Bool := #[false, true, true, true, false, false]

def addTape : Array Bool := #[false, true, true, false, true, true, true, false, false, false]

--#eval run 10 (makeTM 0 (run 10 (makeTM 0 addTape 0) TMadd).t 0) TMsucc
--#eval run 10 (makeTM 0 (run 10 (makeTM 0 addTape 0) TMsucc).t 0) TMadd

--#eval verifyTape addTape.size (run 10 (makeTM 0 (run 10 (makeTM 0 addTape 0) TMadd).t 0) TMsucc).t (run 10 (makeTM 0 (run 10 (makeTM 0 addTape 0) TMsucc).t 0) TMadd).t true

--#eval (run 10 (makeTM 0 #[false, true, true, true, false] 0) TMsucc).t
#eval interface 10 addTape TMadd

def stateCountTM (h : Nat) (t : Array Bool) (q : Int) : TMstate :=
  match t[h], q with
  | true, 0 => makeTMstate 0 false 1
  | false, 0 => makeTMstate 1 true 1
  | true, 1 => makeTMstate 1 false 1
  | false, 1 => makeTMstate 2 false 1
  | true, 2 => makeTMstate 2 false 1
  | false, 2 => makeTMstate 3 false 1
  | true, 3 => makeTMstate 3 false 1
  | false, 3 => makeTMstate 4 false 1
  | true, 4 => makeTMstate 4 false 1 --error
  | false, 4 => makeTMstate 5 false 1
  | true, 5 => makeTMstate (-1) true 1
  | false, 5 => makeTMstate 6 false 1
  | true, 6 => makeTMstate 1 false 1
  | false, 6 => makeTMstate 7 false 1
  | true, 7 => makeTMstate 8 true (-1)
  | false, 7 => makeTMstate (-1) false 0 --program end
  | true, 8 => makeTMstate 9 true 1
  | false, 8 => makeTMstate 8 false (-1)
  | true, 9 => makeTMstate (-1) true 0 --error
  | false, 9 => makeTMstate 10 true 1
  | true, 10 => makeTMstate 11 false 1
  | false, 10 => makeTMstate 10 false 1
  | true, 11 => makeTMstate 11 false 1
  | false, 11 => makeTMstate 1 false 1
  | _, _ => makeTMstate (-1) false 0


def succEncoding : Array Bool :=
#[false,
  false, true, false, true, true, false, true, true, true, false, true, false, false, 
  true, true, false, true, false, true, false, true, true, false, false, false, 
  true, false, true, false, true, false, true, false, true, false, false, 
  true, true, false, true, false, true, true, true, false, true, false, false, false, false]

--#eval succEncoding.size

def addEncoding : Array Bool :=
#[false,
  false, true, false, true, true, false, true, true, true, true, true, false, true, false, false,
  true, true, false, true, false, true, false, true, true, false, false, false,
  true, false, true, false, true, false, true, false, true, false, false,
  true, true, false, true, false, true, true, false, true, false, false, false,
  true, true, false, true, false, true, false, true, true, false, true, false, false,
  true, true, false, true, true, false, true, true, true, false, true, true, false, false, false,
  true, true, true, false, true, false, true, true, false, true, true, true, true, true, false, true, true, false, false,
  true, true, false, true, true, false, true, true, true, true, true, false, true, true, false, false, false, false]

#eval addEncoding.size

--#eval (run 419 (makeTM 1 addEncoding 0) stateCountTM).t

def stateCountEncoding : Array Bool :=
#[false, false, true, false, true, false, false, true, true, false, false,
  true, true, false, true, false, true, false, true, false, false, false,
  true, false, true, false, true, false, true, false, true, true, false, false,
  true, true, false, true, false, true, true, false, true, true, false, false, false,
  true, true, false, true, false, true, false, true, true, false, true, true, false, false,
  true, true, false, true, false, true, true, true, false, true, true, false, false, false,
  true, true, true, false, true, false, true, false, true, true, true, false, true, true, false, false,
  true, true, false, true, false, true, true, true, true, false, true, true, false, false, false,
  true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, true, false, false,
  true, true, false, true, false, true, true, true, true, true, false, true, true, false, false, false,
  true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false,
  true, true, false, true, false, true, true, true, true, true, true, false, true, true, false, false, false,
  true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, false,
  true, true, false, true, false, true, true, true, true, true, true, true, false, true, true, false, false, false,
  true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false,
  true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, false, false, false,
  true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false,
  true, true, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, false, false,
  true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false,
  true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, false, true, false, false, false,
  true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, false, false,
  true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, false, false, false,
  true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, false, false,
  true, true, false, true, false, true, false, true, true, false, false, false, false]

#eval stateCountEncoding.size

--#eval tapeToInt (interface 4657 stateCountEncoding stateCountTM)
--#eval [false, true, false].get! 2
--#eval [false, true, false]

def zeroTape := #[false, false]

--axiom zero_to_tm : 0 = tapeToInt 3 #[false, false, false, false]

axiom zero_to_tm : intToTape 0 = #[false, false]

theorem tm_to_zero : #[false, false] = intToTape 0 := by
  rw [zero_to_tm]

axiom succ_in_tm (n : Nat) : intToTape (Nat.succ n) = (interface (n+2) (intToTape n) TMsucc)

theorem TMsucc_in_nat (n : Nat) : (interface (n+2) (intToTape n) TMsucc) = intToTape (Nat.succ n) := by
  rw [succ_in_tm]

--axiom TM_succ_evals (n : Nat ): (interface (n+2) (intToTape n) TMsucc) = #[false, true{n times}, false]

#eval tapeToInt #[false, true, true, false]

theorem oneTMrep : intToTape (Nat.succ 0) = (interface (2) (intToTape 0) TMsucc) := by
  rw [succ_in_tm]

theorem one_eq_succ_zero: 1 = Nat.succ 0 := by
  rw [Nat.succ_eq_add_one]

#eval interface 2 #[false, false] TMsucc
#eval intToTape 1

theorem one_to_tape : intToLTape (1) = [false, true, false] := by
  unfold intToLTape
  unfold intToLTapeHelp
  unfold intToLTapeHelp
  simp

def listTapeSucc (t : List Bool) : List Bool :=
  false :: (true :: (t.eraseIdx 0))

#eval listTapeSucc [false, true, true, false]

theorem proof_of_concept : intToLTape (Nat.succ 0) = listTapeSucc [false, false] := by
  rw [Nat.succ_eq_add_one]
  rw [Nat.zero_add]
  unfold intToLTape
  unfold intToLTapeHelp
  unfold intToLTapeHelp
  unfold listTapeSucc
  unfold List.eraseIdx
  simp

--1 = tapeToInt 3 #[false, true, false, false]
--1 = tapeToInt 3 
  
 -- succ_eq_add_one succ n = n + 1