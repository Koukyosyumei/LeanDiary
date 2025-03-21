import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Chapter2.Imp

/-!
  This module defines equivalence between commands in a simple imperative language (`Imp`).
  The language operates over a state modeled as a mapping from variable names to natural numbers
  and includes an inductively defined evaluation relation (`CEval`) that specifies its operational
  semantics.

  The core notion of command equivalence (`cequiv`) ensures that two commands produce the same
  final state given any initial state. Several fundamental equivalences are proven, demonstrating
  the behavior of `skip` in sequences.
-/

namespace Equiv

def aequiv (a₁ a₂: Imp.AExp) : Prop :=
  ∀ (st :Imp.State), ∀ (n : ℕ),
  Imp.AEval st a₁ n ↔ Imp.AEval st a₂ n

def bequiv (b₁ b₂: Imp.BExp) : Prop :=
  ∀ (st :Imp.State), ∀ (b : Bool),
  Imp.BEval st b₁ b ↔ Imp.BEval st b₂ b

/--
Defines when two commands `c₁` and `c₂` are equivalent.
Two commands are equivalent if, for any initial state `st` and final state `st'`,
executing `c₁` in `st` results in `st'` if and only if executing `c₂` in `st` results in `st'`.

- Parameters:
  - `c₁`, `c₂`: Commands to compare.
- Returns:
  - A `Prop` stating that `c₁` and `c₂` always produce the same final state for any initial state.
-/
def cequiv (c₁ c₂ : Imp.Command) : Prop :=
    ∀ (st st' : Imp.State),
    Imp.CEval st c₁ st' ↔ Imp.CEval st c₂ st'

theorem double_negation:
  ∀ (bexp : Imp.BExp), bequiv bexp (.not (.not bexp)) := by
  intro bexp
  rw[bequiv]
  intro st b
  constructor
  . intro h
    apply Imp.BEval.not at h
    apply Imp.BEval.not at h
    simp_all
  . intro h
    cases h
    case not hb hc =>
      cases hc
      case not b hn =>
        simp_all

/--
Executing `skip` does not modify the state.
This follows directly from the operational semantics of `skip`.

- Parameters:
  - `st`: The initial state.
- Returns:
  - A proof that evaluating `skip` in `st` results in `st` unchanged.
-/
theorem skip_preserves_state:
  ∀ (st: Imp.State), Imp.CEval st Imp.Command.skip st := by
  apply Imp.CEval.skip

/--
For any command `c`, the sequence `(skip; c)` is equivalent to `c`.

This theorem shows that placing `skip` before `c` has no effect.

- Parameters:
  - `c`: A command in the Imp language.
- Returns:
  - A proof that `cequiv (.seq .skip c) c` holds.
-/
theorem skip_left:
  ∀ (c: Imp.Command), cequiv (.seq .skip c) c := by
  intro c
  -- breaking the Imp.Statement into two directions
  rw [cequiv]
  intros st st'
  constructor
  -- forward (→)
  . intro h
    -- Since `h` is a proof about a sequence evaluation, it must have been constructed using the `seq` rule.
    -- This breaks `h` down into its components.
    cases h
    -- This pattern matches the `seq` constructor, giving us:
    --     `st''`: An intermediate Imp.State after executing skip
    --     `h_skip`: A proof that `Imp.CEval Imp.Command.skip st st''`
    --     `h_c`: A proof that `Imp.CEval c st'' st'`
    case seq st'' h_skip h_c =>
        cases h_skip
        -- Matches the `skip` constructor
        case skip =>
            exact h_c
  -- backward (←)
  . intro h
    apply Imp.CEval.seq
    . apply Imp.CEval.skip
    . exact h

/--
For any command `c`, the sequence `(c; skip)` is equivalent to `c`.

This theorem shows that placing `skip` after `c` has no effect.

- Parameters:
  - `c`: A command in the Imp language.
- Returns:
  - A proof that `cequiv (.seq c .skip) c` holds.
-/
theorem skip_right:
    ∀ (c: Imp.Command), cequiv (.seq c .skip) c := by
    intro c
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case seq st'' h_c h_skip =>
        cases h_skip
        case skip =>
            exact h_c
    . intro h
      apply Imp.CEval.seq
      . exact h
      . apply Imp.CEval.skip

/--
If the boolean condition `b` is `true`, then the `if` statement `if b then c₁ else c₂`
is equivalent to executing `c₁` alone.

This theorem formally proves that when the condition evaluates to `true`,
the `if` command behaves exactly like `c₁`.

- Parameters:
  - `b`: A boolean condition.
  - `c₁`, `c₂`: Commands in the Imp language.
  - `htrue`: A proof that `b = true`.
- Returns:
  - A proof that `cequiv (.if_ b c₁ c₂) c₁` holds.
-/
theorem if_true:
    ∀ (b: Imp.BExp), ∀ (c₁ c₂ : Imp.Command), bequiv b Imp.BExp.btrue → cequiv (.if_ b c₁ c₂) c₁ := by
    intros b c₁ c₂ htrue
    rw[cequiv]
    rw[bequiv] at htrue
    intros st st'
    constructor
    . intro h
      cases h
      case if_true hbeval hc =>
        exact hc
      case if_false hbeval hc =>
        -- .mp is a method used to apply modus ponens
        -- For a bi-implication h : P ↔ Q, h.mp gives the forward direction P → Q
        have h_contra := (htrue st false).mp hbeval
        cases h_contra
    . intro h
      apply Imp.CEval.if_true
      . have true_eval : Imp.BEval st Imp.BExp.btrue true := Imp.BEval.btrue st
        have b_eval : Imp.BEval st b true := (htrue st true).mpr true_eval
        exact b_eval
      . exact h

/--
If the boolean condition `b` is `false`, then the `if` statement `if b then c₁ else c₂`
is equivalent to executing `c₂` alone.

This theorem formally proves that when the condition evaluates to `false`,
the `if` command behaves exactly like `c₂`.

- Parameters:
  - `b`: A boolean condition.
  - `c₁`, `c₂`: Commands in the Imp language.
  - `hfalse`: A proof that `b = false`.
- Returns:
  - A proof that `cequiv (.if_ b c₁ c₂) c₂` holds.
-/
theorem if_false:
    ∀ (b: Imp.BExp), ∀ (c₁ c₂ : Imp.Command), bequiv b Imp.BExp.bfalse → cequiv (.if_ b c₁ c₂) c₂ := by
    intros b c₁ c₂ hfalse
    rw[cequiv]
    rw[bequiv] at hfalse
    intros st st'
    constructor
    . intro h
      cases h
      case if_true beval hc =>
        have h_contra := (hfalse st true).mp beval
        cases h_contra
      case if_false beval hc =>
        exact hc
    . intro h
      apply Imp.CEval.if_false
      . have false_eval : Imp.BEval st Imp.BExp.bfalse false := Imp.BEval.bfalse st
        have b_eval : Imp.BEval st b false := (hfalse st false).mpr false_eval
        exact b_eval
      . exact h

/--
Swapping the branches of an `if` statement with a negated condition does not change its behavior.

This theorem proves that `if b then c₁ else c₂` is equivalent to `if ¬b then c₂ else c₁`.
Since `b` and `¬b` are always complementary, the execution of the two commands remains identical.

- Parameters:
  - `b`: A boolean condition.
  - `c₁`, `c₂`: Commands in the Imp language.
- Returns:
  - A proof that `cequiv (.if_ b c₁ c₂) (.if_ (¬b) c₂ c₁)` holds.
-/
theorem swap_if_branches:
    ∀ (b : Imp.BExp), ∀ (c₁ c₂ : Imp.Command), cequiv (.if_ b c₁ c₂) (.if_ (.not b) c₂ c₁) := by
    intros b c₁ c₂
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case if_true hb hc =>
        apply Imp.CEval.if_false
        apply Imp.BEval.not at hb
        exact hb
        exact hc
      case if_false hb hc =>
        apply Imp.CEval.if_true
        apply Imp.BEval.not at hb
        exact hb
        exact hc
    . intro h
      cases h
      case if_true hb hc =>
        apply Imp.CEval.if_false
        apply Imp.BEval.not at hb
        rw[<-double_negation] at hb
        exact hb
        exact hc
      case if_false hb hc =>
        apply Imp.CEval.if_true
        apply Imp.BEval.not at hb
        rw[<-double_negation] at hb
        exact hb
        exact hc

/--
A `while` loop with a `false` condition is equivalent to `skip`.

Since the loop condition is always false, the loop body never executes,
and execution proceeds as if no loop were present, which is exactly
the behavior of `skip`.

- Parameters:
  - `c`: A command representing the loop body.
- Returns:
  - A proof that `cequiv (.while false c) .skip` holds.
-/
theorem while_false:
    ∀ (c : Imp.Command), cequiv (.while false c) .skip := by
    intros c₁
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case while_false _ =>
        apply Imp.CEval.skip
    . intro h
      cases h
      case skip =>
        apply Imp.CEval.while_false

theorem while_true_nonterm :
  ∀ (c: Imp.Command), ∀ (st₁ st₂: Imp.State), ¬Imp.CEval (.while true c) st₁ st₂ := by
  intros c st₁ st₂ h
  generalize e : Imp.Command.while true c = c' at h
  induction h <;>
  cases e
  next ih =>
    apply ih
    rfl

theorem while_true : ∀ (c: Imp.Command),
  cequiv (.while true c) (.while true .skip) := by
  intros c
  rw[cequiv]
  intros st₁ st₂
  constructor
  . intro h
    apply while_true_nonterm at h
    contradiction
  . intro h
    apply while_true_nonterm at h
    contradiction

theorem loop_unrolling : ∀ (c: Imp.Command), ∀ (b : Bool),
  cequiv (.while b c) (.if_ b (.seq c (.while b c)) .skip) := by
  intros c b
  rw[cequiv]
  intros st₁ st₂
  constructor
  . intro h
    cases b
    case false =>
      apply Imp.CEval.if_false
      rw[while_false] at h
      exact false
      rw[while_false] at h
      exact h
    case true =>
      apply while_true_nonterm at h
      contradiction
  . intro h
    cases b
    case true =>
      cases h
      case if_true h_seq =>
        cases h_seq
        case seq st₃ hc hw =>
          apply while_true_nonterm at hw
          contradiction
    case false =>
      cases h
      case if_false b' hs =>
        rw[while_false]
        exact hs

theorem seq_assoc:
    ∀ (c₁ c₂ c₃ : Imp.Command), cequiv (.seq (.seq c₁ c₂) c₃) (.seq c₁ (.seq c₂ c₃)) := by
    intros c₁ c₂ c₃
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case seq st'' hs hc =>
        cases hs
        case seq st1 h1 h2 =>
            apply Imp.CEval.seq
            . exact h1
            apply Imp.CEval.seq
            . exact h2
            . exact hc
    . intro h
      cases h
      case seq st'' hs hc =>
        cases hc
        case seq st1 h1 h2 =>
            apply Imp.CEval.seq
            apply Imp.CEval.seq
            .exact hs
            .exact h1
            .exact h2

lemma h_eq (st: Imp.State) (x : String) : Imp.set st x (Imp.get st x) = st := by
    funext y
    unfold Imp.set Imp.get
    by_cases h: y = x
    {
        rw[if_pos h]
        rw[h]
    }
    {
        rw[if_neg h]
    }

theorem identify_assignment : ∀ (x : String), cequiv (.assignvar x x) .skip := by
  intro x
  rw[cequiv]
  intros st st'
  constructor
  .intro h
   cases h
   case assignvar =>
     rw[h_eq]
     apply Imp.CEval.skip
  .intro h
   cases h
   case skip =>
     nth_rewrite 2 [← h_eq st x]
     apply Imp.CEval.assignvar

end Equiv
