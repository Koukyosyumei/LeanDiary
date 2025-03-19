import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- A `state` can be modeled as a function mapping variable names
-- to values (e.g., natural numbers in this tutorial)
def state := String -> ℕ

-- Retrive the value of a variable in the state
def get (st: state) (x : String) : ℕ := st x

-- Update the state with a new value for a variable
def set (st: state) (x : String) (v: ℕ) : state :=
  fun y => if y = x then v else st y

-- Syntax of commands
inductive com: Type
| skip: com                          -- nop
| assign (x : String) (a: ℕ) : com   -- x := a
| seq (c1 c2 : com) : com            -- c1; c2
| if_ (b : Bool) (c1 c2 : com) : com -- if b then c1 else c2
| while (b : Bool) (c : com) : com   -- while b do c

-- State transition
inductive ceval : com -> state -> state -> Prop
| E_Skip : ∀ (st : state),
    ceval com.skip st st
| E_Assign : ∀ (st : state) (x : String) (n : ℕ),
    ceval (com.assign x n) st (set st x n)
| E_Seq : ∀ (c1 c2 : com) (st st' st'' : state),
    ceval c1 st st' →
    ceval c2 st' st'' →
    ceval (com.seq c1 c2) st st''
| E_IfTrue : ∀ (st st' : state) (b : Bool) (c1 c2 : com),
    b = true → ceval c1 st st' → ceval (com.if_ b c1 c2) st st'
| E_IfFalse : ∀ (st st' : state) (b : Bool) (c1 c2 : com),
    b = false → ceval c2 st st' → ceval (com.if_ b c1 c2) st st'
| E_WhileFalse : ∀ (st : state) (b : Bool) (c : com),
    b = false → ceval (com.while b c) st st
| E_WhileTrue : ∀ (st st' st'' : state) (b : Bool) (c : com),
    b = true → ceval c st st' → ceval (com.while b c) st' st'' → ceval (com.while b c) st st''

-- Executing `skip` does not change the state
-- This directly follows from the `E_Skip` rule
theorem skip_preserves_state (st : state) :
  ceval com.skip st st := by
  apply ceval.E_Skip

-- Proving a command equivalence

-- ∀c, (skip; c) is equivalent to c
theorem skip_left (c : com) (st st' : state) :
  ceval (com.seq com.skip c) st st' ↔ ceval c st st' := by
  -- breaking the statement into two directions
  constructor
  -- forward (→)
  . intro h
    cases h
    case E_Seq st'' h_skip h_c =>
        cases h_skip
        case E_Skip =>
            exact h_c
  -- backward (←)
  . intro h
    apply ceval.E_Seq
    . apply ceval.E_Skip
    . exact
